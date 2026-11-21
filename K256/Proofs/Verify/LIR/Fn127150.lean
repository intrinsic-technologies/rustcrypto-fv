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

theorem rest_l127150 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127150 bytes_l127150) (entryMap (live .l127150))
      13 0x127150 bytes_l127150 b_l127150 := by
  have f0 : InstrSpec 0x127150 [0x55] (PushPre 0x127150 1) (pushR64Effect 0x127150 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x127150 1 5).toInstrSpec (push_r64_effect_step 0x127150 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x127151 [0x41, 0x57] (PushPre 0x127151 2) (pushR64Effect 0x127151 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x127151 2 15).toInstrSpec (push_r64_rex_effect_step 0x127151 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x127153 [0x41, 0x56] (PushPre 0x127153 2) (pushR64Effect 0x127153 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x127153 2 14).toInstrSpec (push_r64_rex_effect_step 0x127153 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x127155 [0x41, 0x55] (PushPre 0x127155 2) (pushR64Effect 0x127155 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x127155 2 13).toInstrSpec (push_r64_rex_effect_step 0x127155 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x127157 [0x41, 0x54] (PushPre 0x127157 2) (pushR64Effect 0x127157 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x127157 2 12).toInstrSpec (push_r64_rex_effect_step 0x127157 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x127159 [0x53] (PushPre 0x127159 1) (pushR64Effect 0x127159 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x127159 1 3).toInstrSpec (push_r64_effect_step 0x127159 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x12715a [0x48, 0x81, 0xEC, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12715a) (subR64Imm32Effect 0x12715a 4 0x88)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x12715a 4 0x88).toInstrSpec (sub_r64_imm32_effect_step 0x12715a 0x48 0xec 0x88 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x127161 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x127161) (movR64R64Effect 0x127161 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x127161 3 7).toInstrSpec (mov_r64_r64_effect_step 0x127161 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x127164 [0x8B, 0x6A, 0x08] (LoadPre 0x127164 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x127164 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x127164 5 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR32M32LowEffect_footprint 0x127164 5 (.base 2 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x127164 5 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x127167 [0x44, 0x8B, 0x7E, 0x1C] (LoadPre 0x127167 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x127167 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x127167 15 (.base 6 (.d8 0x1c)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x127167 15 (.base 6 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x127167 0x44 (by decide) 7 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x12716b [0x45, 0x89, 0xFD] (fun s => s.RIP = 0x12716b) (movR32R32Effect 0x12716b 3 13 15)
      [.gpr 15] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x12716b 3 13 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x12716b 0x45 0xfd (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12716e [0x41, 0x01, 0xED] (fun s => s.RIP = 0x12716e) (addR32R32Effect 0x12716e 3 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (addR32R32Effect_footprint 0x12716e 3 13 5).toInstrSpec (add_r32_r32_rex_effect_step 0x12716e 0x41 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127151) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127153) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127155) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127157) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127159) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12715a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127161) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127164) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127167) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12716b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 73), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12716e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f11 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 77) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 75), (14, 14), (15, 71), (16, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127171) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 78) (jcc_rel32_effect_step 0x127171 2 0x233) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127150 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127150 :=
  Rest.liftedBlock (rest_l127150 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127150 x hx)

theorem rest_l127177 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127177 bytes_l127177) (entryMap (live .l127177))
      8 0x127177 bytes_l127177 b_l127177 := by
  have f0 : InstrSpec 0x127177 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x127177) (movR64R64Effect 0x127177 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x127177 14 6).toInstrSpec (mov_r64_r64_effect_step 0x127177 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12717a [0x48, 0x8B, 0x36] (LoadPre 0x12717a (fun s => AddrMode.addr (.base 6 .none) s (0x12717a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12717a 6 (.base 6 .none))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12717a 6 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12717a 0x48 (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12717d [0x4D, 0x8B, 0x66, 0x08] (LoadPre 0x12717d (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x12717d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12717d 12 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x12717d 12 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12717d 0x4d (by decide) 4 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x127181 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x127181) (leaR64Effect 0x127181 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x127181 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x127181 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127186 [0x48, 0x89, 0x74, 0x24, 0x40] (StorePre 0x127186 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x127186 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127186 6 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x127186 6 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x127186 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12718b [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x12718b) (movR64R64Effect 0x12718b 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12718b 2 12).toInstrSpec (mov_r64_r64_effect_step 0x12718b 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12718e [0x44, 0x89, 0xE9] (fun s => s.RIP = 0x12718e) (movR32R32Effect 0x12718e 3 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x12718e 3 1 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x12718e 0x44 0xe9 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x127191 [0xE8, 0xBA, 0x0A, 0x00, 0x00] (PushPre 0x127191 5) (callEffect (fun _ => 0x127c50) 0x127196)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x127191 0x127c50 0x127196).toInstrSpec (call_rel32_effect_step 0x127191 0xaba (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12717a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12717d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127181) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127186) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12718b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(2, 62), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12718e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 64), (2, 62), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127191) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 64), (2, 62), (3, 3), (4, 66), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c50) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l127177 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127177 :=
  Rest.liftedBlock (rest_l127177 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127177 x hx)

theorem rest_l127196 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127196 bytes_l127196) (entryMap (live .l127196))
      3 0x127196 bytes_l127196 b_l127196 := by
  have f0 : InstrSpec 0x127196 [0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x127196 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x127196 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x127196 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x127196 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x127196 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12719a [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x12719a) (cmpR32Imm8Effect 0x12719a 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x12719a 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x12719a 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12719a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12719d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x12719d 5 0x22) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127196 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127196 :=
  Rest.liftedBlock (rest_l127196 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127196 x hx)

theorem rest_l12719f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12719f bytes_l12719f) (entryMap (live .l12719f))
      7 0x12719f bytes_l12719f b_l12719f := by
  have f0 : InstrSpec 0x12719f [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x12719f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12719f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12719f 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12719f 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x12719f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1271a4 [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x1271a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1271a4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1271a4 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1271a4 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1271a4 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1271a9 [0x49, 0x89, 0x06] (StorePre 0x1271a9 3 (fun s => AddrMode.addr (.base 14 .none) s (0x1271a9 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1271a9 0 (.base 14 .none))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x1271a9 0 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1271a9 0x49 (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1271ac [0x49, 0x89, 0x4E, 0x08] (StorePre 0x1271ac 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1271ac + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1271ac 1 (.base 14 (.d8 0x8)))
      [.gpr 1, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x1271ac 1 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1271ac 0x49 (by decide) 1 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1271b0 [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x1271b0 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1271b0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1271b0 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1271b0 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1271b0 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1271b4 [0x48, 0x83, 0xF8, 0x3F] (fun s => s.RIP = 0x1271b4) (cmpR64Imm8Effect 0x1271b4 0 0x3f)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1271b4 0 0x3f).toInstrSpec (cmp_r64_imm8_effect_step 0x1271b4 0x48 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271a4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271a9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271ac) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271b0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271b4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271b8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x1271b8 6 0x4c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12719f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12719f :=
  Rest.liftedBlock (rest_l12719f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12719f x hx)

theorem rest_l1271ba [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1271ba bytes_l1271ba) (entryMap (live .l1271ba))
      2 0x1271ba bytes_l1271ba b_l1271ba := by
  have f0 : InstrSpec 0x1271ba [0xB8, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1271ba) (movR32Imm32Effect 0x1271ba 5 0 0x6)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1271ba 5 0 0x6).toInstrSpec (mov_r32_imm32_effect_step 0x1271ba 0xb8 (by decide) 0x6) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271bf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x1271bf 0x61 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1271ba [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1271ba :=
  Rest.liftedBlock (rest_l1271ba code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1271ba x hx)

theorem rest_l1271c1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1271c1 bytes_l1271c1) (entryMap (live .l1271c1))
      14 0x1271c1 bytes_l1271c1 b_l1271c1 := by
  have f0 : InstrSpec 0x1271c1 [0x8B, 0x54, 0x24, 0x0C] (LoadPre 0x1271c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1271c1 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1271c1 2 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1271c1 2 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x1271c1 2 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1271c5 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1271c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1271c5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1271c5 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1271c5 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1271c5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1271ca [0x48, 0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x1271ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1271ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1271ca 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1271ca 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1271ca 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1271cf [0x48, 0x8B, 0x74, 0x24, 0x20] (LoadPre 0x1271cf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1271cf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1271cf 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1271cf 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1271cf 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1271d4 [0x48, 0x89, 0x74, 0x24, 0x48] (StorePre 0x1271d4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1271d4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1271d4 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1271d4 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x1271d4 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1271d9 [0x48, 0x8B, 0x74, 0x24, 0x28] (LoadPre 0x1271d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1271d9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1271d9 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1271d9 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1271d9 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1271de [0x48, 0x89, 0x74, 0x24, 0x50] (StorePre 0x1271de 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1271de + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1271de 6 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1271de 6 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x1271de 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1271e3 [0x48, 0x8B, 0x74, 0x24, 0x30] (LoadPre 0x1271e3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1271e3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1271e3 6 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1271e3 6 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1271e3 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1271e8 [0x48, 0x89, 0x74, 0x24, 0x58] (StorePre 0x1271e8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1271e8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1271e8 6 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1271e8 6 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x1271e8 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1271ed [0x48, 0x8B, 0x74, 0x24, 0x38] (LoadPre 0x1271ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1271ed + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1271ed 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1271ed 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1271ed 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1271f2 [0x48, 0x89, 0x74, 0x24, 0x60] (StorePre 0x1271f2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1271f2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1271f2 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1271f2 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x1271f2 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1271f7 [0x49, 0xB9, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x1271f7) (movR64Imm64Effect 0x1271f7 9 0xffffffff00000000)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x1271f7 9 0xffffffff00000000).toInstrSpec (mov_r64_imm64_effect_step 0x1271f7 0x49 0xb9 (by decide) (by decide) 0xffffffff00000000) pre_rip
  have f12 : InstrSpec 0x127201 [0x49, 0x21, 0xF9] (fun s => s.RIP = 0x127201) (andR64R64Effect 0x127201 9 7)
      [.gpr 9, .gpr 7] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x127201 9 7).toInstrSpec (and_r64_r64_effect_step 0x127201 0x49 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271c5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271ca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (7, 57), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271cf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 59), (7, 57), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271d4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 59), (7, 57), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271d9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 62), (7, 57), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271de) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 62), (7, 57), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271e3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 65), (7, 57), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271e8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 65), (7, 57), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271ed) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 68), (7, 57), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271f2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 68), (7, 57), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1271f7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 68), (7, 57), (9, 71), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127201) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 68), (7, 57), (9, 73), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127204) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 75) (jmp_rel8_effect_step 0x127204 0x2a (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1271c1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1271c1 :=
  Rest.liftedBlock (rest_l1271c1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1271c1 x hx)

theorem rest_l127206 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127206 bytes_l127206) (entryMap (live .l127206))
      5 0x127206 bytes_l127206 b_l127206 := by
  have f0 : InstrSpec 0x127206 [0x48, 0xFF, 0xC0] (fun s => s.RIP = 0x127206) (incR64Effect 0x127206 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (incR64Effect_footprint 0x127206 0).toInstrSpec (inc_r64_effect_step 0x127206 0x48 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127209 [0x49, 0x89, 0x46, 0x10] (StorePre 0x127209 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x127209 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127209 0 (.base 14 (.d8 0x10)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x127209 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x127209 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12720d [0x45, 0x8B, 0x7E, 0x18] (LoadPre 0x12720d (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x12720d + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x12720d 15 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x12720d 15 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x12720d 0x45 (by decide) 7 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x127211 [0x45, 0x39, 0xFD] (fun s => s.RIP = 0x127211) (cmpR32R32Effect 0x127211 3 13 15)
      [.gpr 13, .gpr 15] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x127211 3 13 15).toInstrSpec (cmp_r32_r32_rex_effect_step 0x127211 0x45 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127209) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12720d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127211) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127214) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x127214 6 0x65) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127206 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127206 :=
  Rest.liftedBlock (rest_l127206 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127206 x hx)

theorem rest_l127216 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127216 bytes_l127216) (entryMap (live .l127216))
      3 0x127216 bytes_l127216 b_l127216 := by
  have f0 : InstrSpec 0x127216 [0x41, 0x8D, 0x47, 0x01] (fun s => s.RIP = 0x127216) (leaR32Effect 0x127216 4 0 (.base 15 (.d8 0x1)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (leaR32Effect_footprint 0x127216 4 0 (.base 15 (.d8 0x1))).toInstrSpec (lea_r32_rex_effect_step 0x127216 0x41 (by decide) 0 (.base 15 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12721a [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x12721a) (shlR64Effect 0x12721a 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x12721a 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x12721a 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12721e [0x48, 0x83, 0xC8, 0x03] (fun s => s.RIP = 0x12721e) (orR64Imm8Effect 0x12721e 0 0x3)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x12721e 0 0x3).toInstrSpec (or_r64_imm8_effect_step 0x12721e 0x48 0xc8 0x3 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12721a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12721e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127222) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l127216 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127216 :=
  Rest.liftedBlock (rest_l127216 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127216 x hx)

theorem rest_l127222 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127222 bytes_l127222) (entryMap (live .l127222))
      4 0x127222 bytes_l127222 b_l127222 := by
  have f0 : InstrSpec 0x127222 [0xB9, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127222) (movR32Imm32Effect 0x127222 5 1 0x1)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x127222 5 1 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x127222 0xb9 (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x127227 [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x127227) (xorR32R32Effect 0x127227 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127227 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x127227 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12722a [0x44, 0x89, 0xFA] (fun s => s.RIP = 0x12722a) (movR32R32Effect 0x12722a 3 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x12722a 3 2 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x12722a 0x44 0xfa (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12722d [0x44, 0x89, 0xFF] (fun s => s.RIP = 0x12722d) (movR32R32Effect 0x12722d 3 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x12722d 3 7 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x12722d 0x44 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127227) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (9, 55), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12722a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 57), (3, 3), (4, 4), (9, 55), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12722d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 57), (3, 3), (4, 4), (7, 59), (9, 55), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127230) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l127222 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127222 :=
  Rest.liftedBlock (rest_l127222 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127222 x hx)

theorem rest_l127230 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127230 bytes_l127230) (entryMap (live .l127230))
      14 0x127230 bytes_l127230 b_l127230 := by
  have f0 : InstrSpec 0x127230 [0x89, 0xFE] (fun s => s.RIP = 0x127230) (movR32R32Effect 0x127230 2 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x127230 2 6 7).toInstrSpec (mov_r32_r32_effect_step 0x127230 0xfe (by decide)) pre_rip
  have f1 : InstrSpec 0x127232 [0x4C, 0x09, 0xCE] (fun s => s.RIP = 0x127232) (orR64R64Effect 0x127232 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x127232 6 9).toInstrSpec (or_r64_r64_effect_step 0x127232 0x4c 0xce (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127235 [0x48, 0x8B, 0x7C, 0x24, 0x60] (LoadPre 0x127235 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x127235 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127235 7 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x127235 7 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x127235 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12723a [0x48, 0x89, 0x7B, 0x30] (StorePre 0x12723a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x12723a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12723a 7 (.base 3 (.d8 0x30)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12723a 7 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x12723a 0x48 (by decide) 7 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12723e [0x48, 0x8B, 0x7C, 0x24, 0x58] (LoadPre 0x12723e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12723e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12723e 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12723e 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x12723e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x127243 [0x48, 0x89, 0x7B, 0x28] (StorePre 0x127243 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x127243 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127243 7 (.base 3 (.d8 0x28)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x127243 7 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x127243 0x48 (by decide) 7 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x127247 [0x48, 0x8B, 0x7C, 0x24, 0x48] (LoadPre 0x127247 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x127247 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127247 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x127247 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x127247 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x12724c [0x4C, 0x8B, 0x44, 0x24, 0x50] (LoadPre 0x12724c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x12724c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12724c 8 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x12724c 8 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x12724c 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x127251 [0x4C, 0x89, 0x43, 0x20] (StorePre 0x127251 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x127251 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127251 8 (.base 3 (.d8 0x20)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x127251 8 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x127251 0x4c (by decide) 0 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x127255 [0x48, 0x89, 0x7B, 0x18] (StorePre 0x127255 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x127255 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127255 7 (.base 3 (.d8 0x18)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x127255 7 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x127255 0x48 (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x127259 [0x89, 0x0B] (StorePre 0x127259 2 (fun s => AddrMode.addr (.base 3 .none) s (0x127259 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x127259 1 (.base 3 .none))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127259 1 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x127259 1 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x12725b [0x89, 0x53, 0x04] (StorePre 0x12725b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x12725b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12725b 2 (.base 3 (.d8 0x4)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x12725b 2 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x12725b 2 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x12725e [0x48, 0x89, 0x43, 0x08] (StorePre 0x12725e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12725e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12725e 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12725e 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x12725e 0x48 (by decide) 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x127262 [0x48, 0x89, 0x73, 0x10] (StorePre 0x127262 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x127262 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127262 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x127262 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x127262 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127232) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127235) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12723a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12723e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 60), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127243) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 60), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127247) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12724c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127251) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127255) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127259) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12725b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12725e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127262) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127266) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 73) (by decide) rfl

theorem block_l127230 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127230 :=
  Rest.liftedBlock (rest_l127230 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127230 x hx)

theorem rest_l127266 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127266 bytes_l127266) (entryMap (live .l127266))
      9 0x127266 bytes_l127266 b_l127266 := by
  have f0 : InstrSpec 0x127266 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x127266) (movR64R64Effect 0x127266 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x127266 0 3).toInstrSpec (mov_r64_r64_effect_step 0x127266 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127269 [0x48, 0x81, 0xC4, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127269) (addR64Imm32Effect 0x127269 4 0x88)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x127269 4 0x88).toInstrSpec (add_r64_imm32_effect_step 0x127269 0x48 0xc4 0x88 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127270 [0x5B] (PopPre 0x127270) (popR64Effect 0x127270 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x127270 1 3).toInstrSpec (pop_r64_effect_step 0x127270 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x127271 [0x41, 0x5C] (PopPre 0x127271) (popR64Effect 0x127271 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x127271 2 12).toInstrSpec (pop_r64_rex_effect_step 0x127271 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x127273 [0x41, 0x5D] (PopPre 0x127273) (popR64Effect 0x127273 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x127273 2 13).toInstrSpec (pop_r64_rex_effect_step 0x127273 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x127275 [0x41, 0x5E] (PopPre 0x127275) (popR64Effect 0x127275 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x127275 2 14).toInstrSpec (pop_r64_rex_effect_step 0x127275 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x127277 [0x41, 0x5F] (PopPre 0x127277) (popR64Effect 0x127277 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x127277 2 15).toInstrSpec (pop_r64_rex_effect_step 0x127277 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x127279 [0x5D] (PopPre 0x127279) (popR64Effect 0x127279 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x127279 1 5).toInstrSpec (pop_r64_effect_step 0x127279 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x12727a [0xC3] (RetPre 0x12727a) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12727a).toInstrSpec (ret_effect_step 0x12727a) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127269) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127270) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127271) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127273) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127275) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127277) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127279) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12727a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l127266 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127266 :=
  Rest.liftedBlock (rest_l127266 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127266 x hx)

theorem rest_l12727b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12727b bytes_l12727b) (entryMap (live .l12727b))
      5 0x12727b bytes_l12727b b_l12727b := by
  have f0 : InstrSpec 0x12727b [0x45, 0x89, 0x6E, 0x18] (StorePre 0x12727b 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x12727b + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x12727b 13 (.base 14 (.d8 0x18)))
      [.gpr 13, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x12727b 13 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x12727b 0x45 (by decide) 5 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x12727f [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x12727f) (leaR64Effect 0x12727f 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x12727f 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x12727f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127284 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x127284) (movR64R64Effect 0x127284 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x127284 6 14).toInstrSpec (mov_r64_r64_effect_step 0x127284 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x127287 [0x89, 0xEA] (fun s => s.RIP = 0x127287) (movR32R32Effect 0x127287 2 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x127287 2 2 5).toInstrSpec (mov_r32_r32_effect_step 0x127287 0xea (by decide)) pre_rip
  have f4 : InstrSpec 0x127289 [0xE8, 0xF2, 0x08, 0x00, 0x00] (PushPre 0x127289 5) (callEffect (fun _ => 0x127b80) 0x12728e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x127289 0x127b80 0x12728e).toInstrSpec (call_rel32_effect_step 0x127289 0x8f2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12727f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127284) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 56), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127287) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 58), (3, 3), (4, 4), (5, 5), (6, 56), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127289) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 58), (3, 3), (4, 60), (5, 5), (6, 56), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l12727b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12727b :=
  Rest.liftedBlock (rest_l12727b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12727b x hx)

theorem rest_l12728e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12728e bytes_l12728e) (entryMap (live .l12728e))
      3 0x12728e bytes_l12728e b_l12728e := by
  have f0 : InstrSpec 0x12728e [0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x12728e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12728e + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12728e 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x12728e 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x12728e 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127292 [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x127292) (cmpR32Imm8Effect 0x127292 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x127292 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x127292 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127292) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127295) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x127295 5 0x28) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12728e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12728e :=
  Rest.liftedBlock (rest_l12728e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12728e x hx)

theorem rest_l127297 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127297 bytes_l127297) (entryMap (live .l127297))
      8 0x127297 bytes_l127297 b_l127297 := by
  have f0 : InstrSpec 0x127297 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x127297 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x127297 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127297 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x127297 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x127297 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12729c [0x31, 0xC9] (fun s => s.RIP = 0x12729c) (xorR32R32Effect 0x12729c 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12729c 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x12729c 0xc9 (by decide)) pre_rip
  have f2 : InstrSpec 0x12729e [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x12729e) (movR64R64Effect 0x12729e 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12729e 0 6).toInstrSpec (mov_r64_r64_effect_step 0x12729e 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1272a1 [0x48, 0xC1, 0xE8, 0x20] (fun s => s.RIP = 0x1272a1) (shrR64Effect 0x1272a1 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x1272a1 4 0 32).toInstrSpec (shr_r64_imm8_effect_step 0x1272a1 0x48 0xe8 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1272a5 [0x0F, 0x94, 0xC2] (fun s => s.RIP = 0x1272a5) (atFlags (condHolds 4) (setccR8Effect 0x1272a5 3 2))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (setccR8Effect_footprint 0x1272a5 3 2 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1272a5 4 0xc2 (by decide) (by decide) c)) pre_rip
  have f5 : InstrSpec 0x1272a8 [0xB8, 0x0C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1272a8) (movR32Imm32Effect 0x1272a8 5 0 0xc)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1272a8 5 0 0xc).toInstrSpec (mov_r32_imm32_effect_step 0x1272a8 0xb8 (by decide) 0xc) pre_rip
  have f6 : InstrSpec 0x1272ad [0x4C, 0x8B, 0x54, 0x24, 0x40] (LoadPre 0x1272ad (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1272ad + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272ad 10 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1272ad 10 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1272ad 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12729c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (2, 2), (3, 3), (4, 4), (6, 53), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12729e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (2, 2), (3, 3), (4, 4), (6, 53), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272a1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.fresh (n := 59) f3 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x1272a1 4 0 32 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 55), (2, 2), (3, 3), (4, 4), (6, 53), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272a5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 55), (2, 61), (3, 3), (4, 4), (6, 53), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272a8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 55), (2, 61), (3, 3), (4, 4), (6, 53), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272ad) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 63), (1, 55), (2, 61), (3, 3), (4, 4), (6, 53), (8, 8), (9, 9), (10, 65), (11, 11), (12, 12), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272b2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 67) (jcc_rel8_effect_step 0x1272b2 5 0x5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127297 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127297 :=
  Rest.liftedBlock (rest_l127297 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127297 x hx)

theorem rest_l1272b4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1272b4 bytes_l1272b4) (entryMap (live .l1272b4))
      1 0x1272b4 bytes_l1272b4 b_l1272b4 := by
  have f0 : InstrSpec 0x1272b4 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1272b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1272b4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272b4 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1272b4 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1272b4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272b9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1272b4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1272b4 :=
  Rest.liftedBlock (rest_l1272b4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1272b4 x hx)

theorem rest_l1272b9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1272b9 bytes_l1272b9) (entryMap (live .l1272b9))
      3 0x1272b9 bytes_l1272b9 b_l1272b9 := by
  have f0 : InstrSpec 0x1272b9 [0x88, 0xD1] (fun s => s.RIP = 0x1272b9) (movR8R8Effect 0x1272b9 2 1 2)
      [.gpr 2, .gpr 1] [] [.reg 1, .rip] :=
    (movR8R8Effect_footprint 0x1272b9 2 1 2).toInstrSpec (mov_r8_r8_effect_step 0x1272b9 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1272bb [0x01, 0xC9] (fun s => s.RIP = 0x1272bb) (addR32R32Effect 0x1272bb 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1272bb 2 1 1).toInstrSpec (add_r32_r32_effect_step 0x1272bb 0xc9 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272bb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272bd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x1272bd 0x3f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1272b9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1272b9 :=
  Rest.liftedBlock (rest_l1272b9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1272b9 x hx)

theorem rest_l1272bf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1272bf bytes_l1272bf) (entryMap (live .l1272bf))
      12 0x1272bf bytes_l1272bf b_l1272bf := by
  have f0 : InstrSpec 0x1272bf [0x44, 0x8B, 0x44, 0x24, 0x0C] (LoadPre 0x1272bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1272bf + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1272bf 8 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x1272bf 8 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_effect_step 0x1272bf 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1272c4 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1272c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1272c4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272c4 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1272c4 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1272c4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1272c9 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x1272c9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1272c9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272c9 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1272c9 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1272c9 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1272ce [0x48, 0x8B, 0x54, 0x24, 0x20] (LoadPre 0x1272ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1272ce + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272ce 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1272ce 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1272ce 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1272d3 [0x48, 0x89, 0x54, 0x24, 0x68] (StorePre 0x1272d3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1272d3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1272d3 2 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1272d3 2 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x1272d3 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1272d8 [0x48, 0x8B, 0x54, 0x24, 0x28] (LoadPre 0x1272d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1272d8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272d8 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1272d8 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1272d8 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1272dd [0x48, 0x89, 0x54, 0x24, 0x70] (StorePre 0x1272dd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1272dd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1272dd 2 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1272dd 2 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x1272dd 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1272e2 [0x48, 0x8B, 0x54, 0x24, 0x30] (LoadPre 0x1272e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1272e2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272e2 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1272e2 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1272e2 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1272e7 [0x48, 0x89, 0x54, 0x24, 0x78] (StorePre 0x1272e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1272e7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1272e7 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1272e7 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x1272e7 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1272ec [0x48, 0x8B, 0x54, 0x24, 0x38] (LoadPre 0x1272ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1272ec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272ec 2 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1272ec 2 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1272ec 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1272f1 [0x48, 0x89, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x1272f1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1272f1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1272f1 2 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1272f1 2 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x1272f1 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1272f9 [0x4C, 0x8B, 0x54, 0x24, 0x40] (LoadPre 0x1272f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1272f9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272f9 10 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1272f9 10 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1272f9 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (8, 53), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272c4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (8, 53), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272c9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (6, 57), (8, 53), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272ce) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 59), (3, 3), (4, 4), (6, 57), (8, 53), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272d3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 1), (2, 59), (3, 3), (4, 4), (6, 57), (8, 53), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272d8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 1), (2, 62), (3, 3), (4, 4), (6, 57), (8, 53), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272dd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 1), (2, 62), (3, 3), (4, 4), (6, 57), (8, 53), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272e2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 1), (2, 65), (3, 3), (4, 4), (6, 57), (8, 53), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272e7) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 1), (2, 65), (3, 3), (4, 4), (6, 57), (8, 53), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272ec) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 55), (1, 1), (2, 68), (3, 3), (4, 4), (6, 57), (8, 53), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272f1) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 1), (2, 68), (3, 3), (4, 4), (6, 57), (8, 53), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272f9) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 1), (2, 68), (3, 3), (4, 4), (6, 57), (8, 53), (9, 9), (10, 71), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1272fe) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 73) (by decide) rfl

theorem block_l1272bf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1272bf :=
  Rest.liftedBlock (rest_l1272bf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1272bf x hx)

theorem rest_l1272fe [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1272fe bytes_l1272fe) (entryMap (live .l1272fe))
      15 0x1272fe bytes_l1272fe b_l1272fe := by
  have f0 : InstrSpec 0x1272fe [0x41, 0x8B, 0x7E, 0x18] (LoadPre 0x1272fe (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1272fe + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1272fe 7 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR32M32Effect_footprint 0x1272fe 7 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x1272fe 0x41 (by decide) 7 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127302 [0x41, 0x8B, 0x56, 0x1C] (LoadPre 0x127302 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x127302 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x127302 2 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR32M32Effect_footprint 0x127302 2 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x127302 0x41 (by decide) 2 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x127306 [0x29, 0xD7] (fun s => s.RIP = 0x127306) (subR32R32Effect 0x127306 2 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (subR32R32Effect_footprint 0x127306 2 7 2).toInstrSpec (sub_r32_r32_effect_step 0x127306 0xd7 (by decide)) pre_rip
  have f3 : InstrSpec 0x127308 [0x41, 0x0F, 0x96, 0xC1] (fun s => s.RIP = 0x127308) (atFlags (condHolds 6) (setccR8Effect 0x127308 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x127308 4 9 6).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x127308 6 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f4 : InstrSpec 0x12730c [0x4D, 0x89, 0x16] (StorePre 0x12730c 3 (fun s => AddrMode.addr (.base 14 .none) s (0x12730c + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x12730c 10 (.base 14 .none))
      [.gpr 10, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x12730c 10 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x12730c 0x4d (by decide) 2 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12730f [0x4D, 0x89, 0x66, 0x08] (StorePre 0x12730f 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x12730f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12730f 12 (.base 14 (.d8 0x8)))
      [.gpr 12, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x12730f 12 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x12730f 0x4d (by decide) 4 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x127313 [0x45, 0x89, 0x7E, 0x18] (StorePre 0x127313 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x127313 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x127313 15 (.base 14 (.d8 0x18)))
      [.gpr 15, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x127313 15 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x127313 0x45 (by decide) 7 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x127317 [0x4D, 0x8B, 0x56, 0x10] (LoadPre 0x127317 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x127317 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x127317 10 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x127317 10 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x127317 0x4d (by decide) 2 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x12731b [0x49, 0x83, 0xFA, 0x01] (fun s => s.RIP = 0x12731b) (cmpR64Imm8Effect 0x12731b 10 0x1)
      [.gpr 10] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x12731b 10 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x12731b 0x49 0xfa 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x12731f [0x49, 0x83, 0xD2, 0xFF] (fun s => s.RIP = 0x12731f) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x12731f 10 0xff))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x12731f 10 0xff).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x12731f 0x49 0xd2 0xff c (by decide) (by decide) (by decide))) pre_rip
  have f10 : InstrSpec 0x127323 [0x4D, 0x89, 0x56, 0x10] (StorePre 0x127323 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x127323 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127323 10 (.base 14 (.d8 0x10)))
      [.gpr 10, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x127323 10 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x127323 0x4d (by decide) 2 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x127327 [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x127327) (cmpR32Imm8Effect 0x127327 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x127327 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x127327 0xf9 0x2 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x12732a [0x41, 0x0F, 0x95, 0xC2] (fun s => s.RIP = 0x12732a) (atFlags (condHolds 5) (setccR8Effect 0x12732a 4 10))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 10, .rip] :=
    (setccR8Effect_footprint 0x12732a 4 10 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x12732a 5 0x41 (by decide) 0xc2 (by decide) c)) pre_rip
  have f13 : InstrSpec 0x12732e [0x45, 0x08, 0xCA] (fun s => s.RIP = 0x12732e) (orR8R8Effect 0x12732e 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (orR8R8Effect_footprint 0x12732e 3 10 9).toInstrSpec (or_r8_r8_rex_effect_step 0x12732e 0x45 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127302) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127306) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 59) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127308) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (6, 6), (7, 57), (8, 8), (9, 61), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12730c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (6, 6), (7, 57), (8, 8), (9, 61), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12730f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (6, 6), (7, 57), (8, 8), (9, 61), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127313) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (6, 6), (7, 57), (8, 8), (9, 61), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127317) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (6, 6), (7, 57), (8, 8), (9, 61), (10, 66), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12731b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (6, 6), (7, 57), (8, 8), (9, 61), (10, 66), (11, 11), (12, 12), (14, 14), (15, 15), (16, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12731f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (6, 6), (7, 57), (8, 8), (9, 61), (10, 70), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127323) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (6, 6), (7, 57), (8, 8), (9, 61), (10, 70), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127327) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (6, 6), (7, 57), (8, 8), (9, 61), (10, 70), (11, 11), (12, 12), (14, 14), (15, 15), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12732a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (6, 6), (7, 57), (8, 8), (9, 61), (10, 75), (11, 11), (12, 12), (14, 14), (15, 15), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12732e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 78) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (6, 6), (7, 57), (8, 8), (9, 61), (10, 77), (11, 11), (12, 12), (14, 14), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127331) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 80) (jcc_rel8_effect_step 0x127331 4 0x43) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1272fe [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1272fe :=
  Rest.liftedBlock (rest_l1272fe code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1272fe x hx)

theorem rest_l127333 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127333 bytes_l127333) (entryMap (live .l127333))
      10 0x127333 bytes_l127333 b_l127333 := by
  have f0 : InstrSpec 0x127333 [0x48, 0x8B, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x127333 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x127333 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x127333 2 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x127333 2 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x127333 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12733b [0x48, 0x89, 0x54, 0x24, 0x60] (StorePre 0x12733b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12733b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12733b 2 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12733b 2 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x12733b 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127340 [0x48, 0x8B, 0x54, 0x24, 0x78] (LoadPre 0x127340 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x127340 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127340 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x127340 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x127340 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x127345 [0x48, 0x89, 0x54, 0x24, 0x58] (StorePre 0x127345 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x127345 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127345 2 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x127345 2 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x127345 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12734a [0x48, 0x8B, 0x54, 0x24, 0x68] (LoadPre 0x12734a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x12734a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12734a 2 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12734a 2 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x12734a 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x12734f [0x48, 0x8B, 0x7C, 0x24, 0x70] (LoadPre 0x12734f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x12734f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12734f 7 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12734f 7 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x12734f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x127354 [0x48, 0x89, 0x7C, 0x24, 0x50] (StorePre 0x127354 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x127354 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127354 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x127354 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x127354 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x127359 [0x48, 0x89, 0x54, 0x24, 0x48] (StorePre 0x127359 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x127359 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127359 2 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x127359 2 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x127359 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x12735e [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x12735e) (cmpR32Imm8Effect 0x12735e 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x12735e 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x12735e 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12733b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127340) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127345) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12734a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12734f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127354) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127359) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12735e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127361) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 67) (jcc_rel8_effect_step 0x127361 5 0x30) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127333 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127333 :=
  Rest.liftedBlock (rest_l127333 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127333 x hx)

theorem rest_l127363 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127363 bytes_l127363) (entryMap (live .l127363))
      4 0x127363 bytes_l127363 b_l127363 := by
  have f0 : InstrSpec 0x127363 [0x48, 0x89, 0x43, 0x08] (StorePre 0x127363 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x127363 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127363 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x127363 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x127363 0x48 (by decide) 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x127367 [0x48, 0x89, 0x73, 0x10] (StorePre 0x127367 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x127367 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127367 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x127367 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x127367 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12736b [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x12736b 6 (fun s => AddrMode.addr (.base 3 .none) s (0x12736b + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x12736b 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x12736b 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x12736b (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127367) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12736b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127371) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 56) (jmp_rel32_effect_step 0x127371 0xfffffef0 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l127363 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127363 :=
  Rest.liftedBlock (rest_l127363 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127363 x hx)

theorem rest_l127376 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127376 bytes_l127376) (entryMap (live .l127376))
      7 0x127376 bytes_l127376 b_l127376 := by
  have f0 : InstrSpec 0x127376 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x127376 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x127376 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x127376 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x127376 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x127376 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x12737b [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x12737b) (movR64R64Effect 0x12737b 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12737b 0 2).toInstrSpec (mov_r64_r64_effect_step 0x12737b 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12737e [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x12737e) (shlR64Effect 0x12737e 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x12737e 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x12737e 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x127382 [0x48, 0x83, 0xC8, 0x13] (fun s => s.RIP = 0x127382) (orR64Imm8Effect 0x127382 0 0x13)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x127382 0 0x13).toInstrSpec (or_r64_imm8_effect_step 0x127382 0x48 0xc8 0x13 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127386 [0xB9, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127386) (movR32Imm32Effect 0x127386 5 1 0x1)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x127386 5 1 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x127386 0xb9 (by decide) 0x1) pre_rip
  have f5 : InstrSpec 0x12738b [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x12738b) (xorR32R32Effect 0x12738b 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12738b 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x12738b 0x45 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12737b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12737e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127382) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127386) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 58), (1, 60), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12738b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 58), (1, 60), (2, 2), (3, 3), (4, 4), (7, 7), (9, 62), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12738e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 64) (jmp_rel32_effect_step 0x12738e 0xfffffe9d (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l127376 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127376 :=
  Rest.liftedBlock (rest_l127376 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127376 x hx)

theorem rest_l127393 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127393 bytes_l127393) (entryMap (live .l127393))
      5 0x127393 bytes_l127393 b_l127393 := by
  have f0 : InstrSpec 0x127393 [0x49, 0xB9, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x127393) (movR64Imm64Effect 0x127393 9 0xffffffff00000000)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x127393 9 0xffffffff00000000).toInstrSpec (mov_r64_imm64_effect_step 0x127393 0x49 0xb9 (by decide) (by decide) 0xffffffff00000000) pre_rip
  have f1 : InstrSpec 0x12739d [0x49, 0x21, 0xF1] (fun s => s.RIP = 0x12739d) (andR64R64Effect 0x12739d 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x12739d 9 6).toInstrSpec (and_r64_r64_effect_step 0x12739d 0x49 0xf1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1273a0 [0x44, 0x89, 0xC2] (fun s => s.RIP = 0x1273a0) (movR32R32Effect 0x1273a0 3 2 8)
      [.gpr 8] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x1273a0 3 2 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x1273a0 0x44 0xc2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1273a3 [0x89, 0xF7] (fun s => s.RIP = 0x1273a3) (movR32R32Effect 0x1273a3 2 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x1273a3 2 7 6).toInstrSpec (mov_r32_r32_effect_step 0x1273a3 0xf7 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12739d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (6, 6), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273a0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (6, 6), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273a3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (6, 6), (7, 59), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273a5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 61) (jmp_rel32_effect_step 0x1273a5 0xfffffe86 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l127393 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127393 :=
  Rest.liftedBlock (rest_l127393 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127393 x hx)

theorem rest_l1273aa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1273aa bytes_l1273aa) (entryMap (live .l1273aa))
      4 0x1273aa bytes_l1273aa b_l1273aa := by
  have f0 : InstrSpec 0x1273aa [0x31, 0xC9] (fun s => s.RIP = 0x1273aa) (xorR32R32Effect 0x1273aa 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1273aa 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x1273aa 0xc9 (by decide)) pre_rip
  have f1 : InstrSpec 0x1273ac [0xB8, 0x0C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1273ac) (movR32Imm32Effect 0x1273ac 5 0 0xc)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1273ac 5 0 0xc).toInstrSpec (mov_r32_imm32_effect_step 0x1273ac 0xb8 (by decide) 0xc) pre_rip
  have f2 : InstrSpec 0x1273b1 [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x1273b1) (xorR32R32Effect 0x1273b1 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1273b1 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1273b1 0x45 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273ac) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273b1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (7, 7), (9, 57), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273b4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x1273b4 0xfffffe77 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1273aa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1273aa :=
  Rest.liftedBlock (rest_l1273aa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1273aa x hx)

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

theorem_by block_l127150_eval :
    program.runBlock (dialect code) ⟨.l127150, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127177_eval :
    program.runBlock (dialect code) ⟨.l127177, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127196_eval :
    program.runBlock (dialect code) ⟨.l127196, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12719f_eval :
    program.runBlock (dialect code) ⟨.l12719f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1271ba_eval :
    program.runBlock (dialect code) ⟨.l1271ba, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1271c1_eval :
    program.runBlock (dialect code) ⟨.l1271c1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127206_eval :
    program.runBlock (dialect code) ⟨.l127206, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127216_eval :
    program.runBlock (dialect code) ⟨.l127216, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127222_eval :
    program.runBlock (dialect code) ⟨.l127222, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127230_eval :
    program.runBlock (dialect code) ⟨.l127230, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127266_eval :
    program.runBlock (dialect code) ⟨.l127266, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12727b_eval :
    program.runBlock (dialect code) ⟨.l12727b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12728e_eval :
    program.runBlock (dialect code) ⟨.l12728e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127297_eval :
    program.runBlock (dialect code) ⟨.l127297, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1272b4_eval :
    program.runBlock (dialect code) ⟨.l1272b4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1272b9_eval :
    program.runBlock (dialect code) ⟨.l1272b9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1272bf_eval :
    program.runBlock (dialect code) ⟨.l1272bf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1272fe_eval :
    program.runBlock (dialect code) ⟨.l1272fe, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127333_eval :
    program.runBlock (dialect code) ⟨.l127333, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127363_eval :
    program.runBlock (dialect code) ⟨.l127363, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127376_eval :
    program.runBlock (dialect code) ⟨.l127376, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127393_eval :
    program.runBlock (dialect code) ⟨.l127393, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1273aa_eval :
    program.runBlock (dialect code) ⟨.l1273aa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
