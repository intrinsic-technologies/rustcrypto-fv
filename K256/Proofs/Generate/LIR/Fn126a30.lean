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

theorem rest_l126a30 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126a30 bytes_l126a30) (entryMap (live .l126a30))
      12 0x126a30 bytes_l126a30 b_l126a30 := by
  have f0 : InstrSpec 0x126a30 [0x55] (PushPre 0x126a30 1) (pushR64Effect 0x126a30 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x126a30 1 5).toInstrSpec (push_r64_effect_step 0x126a30 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x126a31 [0x41, 0x57] (PushPre 0x126a31 2) (pushR64Effect 0x126a31 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x126a31 2 15).toInstrSpec (push_r64_rex_effect_step 0x126a31 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x126a33 [0x41, 0x56] (PushPre 0x126a33 2) (pushR64Effect 0x126a33 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x126a33 2 14).toInstrSpec (push_r64_rex_effect_step 0x126a33 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x126a35 [0x41, 0x55] (PushPre 0x126a35 2) (pushR64Effect 0x126a35 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x126a35 2 13).toInstrSpec (push_r64_rex_effect_step 0x126a35 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x126a37 [0x41, 0x54] (PushPre 0x126a37 2) (pushR64Effect 0x126a37 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x126a37 2 12).toInstrSpec (push_r64_rex_effect_step 0x126a37 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x126a39 [0x53] (PushPre 0x126a39 1) (pushR64Effect 0x126a39 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x126a39 1 3).toInstrSpec (push_r64_effect_step 0x126a39 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x126a3a [0x48, 0x81, 0xEC, 0xD8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126a3a) (subR64Imm32Effect 0x126a3a 4 0xd8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x126a3a 4 0xd8).toInstrSpec (sub_r64_imm32_effect_step 0x126a3a 0x48 0xec 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x126a41 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x126a41) (movR64R64Effect 0x126a41 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x126a41 3 7).toInstrSpec (mov_r64_r64_effect_step 0x126a41 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x126a44 [0x44, 0x8B, 0x7E, 0x1C] (LoadPre 0x126a44 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x126a44 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126a44 15 (.base 6 (.d8 0x1c)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x126a44 15 (.base 6 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x126a44 0x44 (by decide) 7 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x126a48 [0x8B, 0x6A, 0x08] (LoadPre 0x126a48 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x126a48 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x126a48 5 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR32M32LowEffect_footprint 0x126a48 5 (.base 2 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x126a48 5 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x126a4b [0x44, 0x01, 0xFD] (fun s => s.RIP = 0x126a4b) (addR32R32Effect 0x126a4b 3 5 15)
      [.gpr 5, .gpr 15] [] [.reg 5, .flags, .rip] :=
    (addR32R32Effect_footprint 0x126a4b 3 5 15).toInstrSpec (add_r32_r32_rex_effect_step 0x126a4b 0x44 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a31) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a33) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a35) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a37) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a39) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a3a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a41) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a44) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a48) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a4b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a4e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 76) (jcc_rel32_effect_step 0x126a4e 2 0x2bc) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126a30 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126a30 :=
  Rest.liftedBlock (rest_l126a30 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126a30 x hx)

theorem rest_l126a54 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126a54 bytes_l126a54) (entryMap (live .l126a54))
      9 0x126a54 bytes_l126a54 b_l126a54 := by
  have f0 : InstrSpec 0x126a54 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x126a54) (movR64R64Effect 0x126a54 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x126a54 13 2).toInstrSpec (mov_r64_r64_effect_step 0x126a54 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126a57 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x126a57) (movR64R64Effect 0x126a57 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x126a57 14 6).toInstrSpec (mov_r64_r64_effect_step 0x126a57 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126a5a [0x48, 0x8B, 0x36] (LoadPre 0x126a5a (fun s => AddrMode.addr (.base 6 .none) s (0x126a5a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x126a5a 6 (.base 6 .none))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x126a5a 6 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x126a5a 0x48 (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126a5d [0x4D, 0x8B, 0x66, 0x08] (LoadPre 0x126a5d (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126a5d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126a5d 12 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x126a5d 12 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x126a5d 0x4d (by decide) 4 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x126a61 [0x48, 0x8D, 0x7C, 0x24, 0x48] (fun s => s.RIP = 0x126a61) (leaR64Effect 0x126a61 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x126a61 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x126a61 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x126a66 [0x48, 0x89, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x126a66 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x126a66 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126a66 6 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126a66 6 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x126a66 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x126a6e [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x126a6e) (movR64R64Effect 0x126a6e 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x126a6e 2 12).toInstrSpec (mov_r64_r64_effect_step 0x126a6e 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x126a71 [0x89, 0xE9] (fun s => s.RIP = 0x126a71) (movR32R32Effect 0x126a71 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x126a71 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x126a71 0xe9 (by decide)) pre_rip
  have f8 : InstrSpec 0x126a73 [0xE8, 0xD8, 0x11, 0x00, 0x00] (PushPre 0x126a73 5) (callEffect (fun _ => 0x127c50) 0x126a78)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x126a73 0x127c50 0x126a78).toInstrSpec (call_rel32_effect_step 0x126a73 0x11d8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a57) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a5a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a5d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a61) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a66) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a6e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 64), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a71) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a73) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 68), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c50) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 70) (by decide) (by decide) rfl rfl

theorem block_l126a54 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126a54 :=
  Rest.liftedBlock (rest_l126a54 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126a54 x hx)

theorem rest_l126a78 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126a78 bytes_l126a78) (entryMap (live .l126a78))
      3 0x126a78 bytes_l126a78 b_l126a78 := by
  have f0 : InstrSpec 0x126a78 [0x8B, 0x54, 0x24, 0x48] (LoadPre 0x126a78 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126a78 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126a78 2 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x126a78 2 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r32_m32_low_effect_step 0x126a78 2 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126a7c [0x83, 0xFA, 0x02] (fun s => s.RIP = 0x126a7c) (cmpR32Imm8Effect 0x126a7c 3 2 0x2)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x126a7c 3 2 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x126a7c 0xfa 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a7c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a7f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x126a7f 5 0x22) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126a78 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126a78 :=
  Rest.liftedBlock (rest_l126a78 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126a78 x hx)

theorem rest_l126a81 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126a81 bytes_l126a81) (entryMap (live .l126a81))
      7 0x126a81 bytes_l126a81 b_l126a81 := by
  have f0 : InstrSpec 0x126a81 [0x48, 0x8B, 0x44, 0x24, 0x50] (LoadPre 0x126a81 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126a81 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126a81 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126a81 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x126a81 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126a86 [0x48, 0x8B, 0x4C, 0x24, 0x58] (LoadPre 0x126a86 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126a86 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126a86 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x126a86 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x126a86 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126a8b [0x49, 0x89, 0x06] (StorePre 0x126a8b 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126a8b + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126a8b 0 (.base 14 .none))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126a8b 0 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x126a8b 0x49 (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x126a8e [0x49, 0x89, 0x4E, 0x08] (StorePre 0x126a8e 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126a8e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126a8e 1 (.base 14 (.d8 0x8)))
      [.gpr 1, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126a8e 1 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x126a8e 0x49 (by decide) 1 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x126a92 [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x126a92 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126a92 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126a92 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126a92 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x126a92 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x126a96 [0x48, 0x83, 0xF8, 0x3F] (fun s => s.RIP = 0x126a96) (cmpR64Imm8Effect 0x126a96 0 0x3f)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x126a96 0 0x3f).toInstrSpec (cmp_r64_imm8_effect_step 0x126a96 0x48 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a86) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a8b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a8e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a92) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a96) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a9a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x126a9a 6 0x4c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126a81 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126a81 :=
  Rest.liftedBlock (rest_l126a81 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126a81 x hx)

theorem rest_l126a9c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126a9c bytes_l126a9c) (entryMap (live .l126a9c))
      2 0x126a9c bytes_l126a9c b_l126a9c := by
  have f0 : InstrSpec 0x126a9c [0xB8, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126a9c) (movR32Imm32Effect 0x126a9c 5 0 0x6)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x126a9c 5 0 0x6).toInstrSpec (mov_r32_imm32_effect_step 0x126a9c 0xb8 (by decide) 0x6) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (7, 7), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126aa1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x126aa1 0x65 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126a9c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126a9c :=
  Rest.liftedBlock (rest_l126a9c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126a9c x hx)

theorem rest_l126aa3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126aa3 bytes_l126aa3) (entryMap (live .l126aa3))
      11 0x126aa3 bytes_l126aa3 b_l126aa3 := by
  have f0 : InstrSpec 0x126aa3 [0x8B, 0x4C, 0x24, 0x4C] (LoadPre 0x126aa3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x126aa3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126aa3 1 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x126aa3 1 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_r32_m32_low_effect_step 0x126aa3 1 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126aa7 [0x48, 0x8B, 0x44, 0x24, 0x50] (LoadPre 0x126aa7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126aa7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126aa7 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126aa7 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x126aa7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126aac [0x48, 0x8B, 0x74, 0x24, 0x58] (LoadPre 0x126aac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126aac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126aac 6 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x126aac 6 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x126aac 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126ab1 [0x48, 0x8B, 0x7C, 0x24, 0x60] (LoadPre 0x126ab1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126ab1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ab1 7 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126ab1 7 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x126ab1 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x126ab6 [0x48, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x126ab6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126ab6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126ab6 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126ab6 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x126ab6 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x126abb [0x48, 0x8B, 0x7C, 0x24, 0x68] (LoadPre 0x126abb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x126abb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126abb 7 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126abb 7 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x126abb 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x126ac0 [0x48, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x126ac0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126ac0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126ac0 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126ac0 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x126ac0 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x126ac5 [0x48, 0x8B, 0x7C, 0x24, 0x70] (LoadPre 0x126ac5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x126ac5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ac5 7 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126ac5 7 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x126ac5 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x126aca [0x48, 0x89, 0x7C, 0x24, 0x18] (StorePre 0x126aca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126aca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126aca 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126aca 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x126aca 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x126acf [0x48, 0x8B, 0x7C, 0x24, 0x78] (LoadPre 0x126acf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126acf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126acf 7 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126acf 7 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x126acf 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x126ad4 [0x48, 0x89, 0x7C, 0x24, 0x20] (StorePre 0x126ad4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126ad4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126ad4 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126ad4 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x126ad4 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126aa7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126aac) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ab1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ab6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126abb) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 62), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ac0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 62), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ac5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 65), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126aca) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 65), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126acf) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ad4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ad9) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 71) (by decide) rfl

theorem block_l126aa3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126aa3 :=
  Rest.liftedBlock (rest_l126aa3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126aa3 x hx)

theorem rest_l126ad9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126ad9 bytes_l126ad9) (entryMap (live .l126ad9))
      3 0x126ad9 bytes_l126ad9 b_l126ad9 := by
  have f0 : InstrSpec 0x126ad9 [0x48, 0xBF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x126ad9) (movR64Imm64Effect 0x126ad9 7 0xffffffff00000000)
      [] [] [.reg 7, .rip] :=
    (movR64Imm64Effect_footprint 0x126ad9 7 0xffffffff00000000).toInstrSpec (mov_r64_imm64_effect_step 0x126ad9 0x48 0xbf (by decide) (by decide) 0xffffffff00000000) pre_rip
  have f1 : InstrSpec 0x126ae3 [0x48, 0x21, 0xF7] (fun s => s.RIP = 0x126ae3) (andR64R64Effect 0x126ae3 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x126ae3 7 6).toInstrSpec (and_r64_r64_effect_step 0x126ae3 0x48 0xf7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ae3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 55), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ae6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x126ae6 0x2d (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126ad9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126ad9 :=
  Rest.liftedBlock (rest_l126ad9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126ad9 x hx)

theorem rest_l126ae8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126ae8 bytes_l126ae8) (entryMap (live .l126ae8))
      5 0x126ae8 bytes_l126ae8 b_l126ae8 := by
  have f0 : InstrSpec 0x126ae8 [0x48, 0xFF, 0xC0] (fun s => s.RIP = 0x126ae8) (incR64Effect 0x126ae8 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (incR64Effect_footprint 0x126ae8 0).toInstrSpec (inc_r64_effect_step 0x126ae8 0x48 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126aeb [0x49, 0x89, 0x46, 0x10] (StorePre 0x126aeb 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126aeb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126aeb 0 (.base 14 (.d8 0x10)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126aeb 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x126aeb 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x126aef [0x45, 0x8B, 0x7E, 0x18] (LoadPre 0x126aef (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126aef + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126aef 15 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x126aef 15 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x126aef 0x45 (by decide) 7 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126af3 [0x44, 0x39, 0xFD] (fun s => s.RIP = 0x126af3) (cmpR32R32Effect 0x126af3 3 5 15)
      [.gpr 5, .gpr 15] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x126af3 3 5 15).toInstrSpec (cmp_r32_r32_rex_effect_step 0x126af3 0x44 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126aeb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126aef) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126af3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126af6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel32_effect_step 0x126af6 6 0x80) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126ae8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126ae8 :=
  Rest.liftedBlock (rest_l126ae8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126ae8 x hx)

theorem rest_l126afc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126afc bytes_l126afc) (entryMap (live .l126afc))
      3 0x126afc bytes_l126afc b_l126afc := by
  have f0 : InstrSpec 0x126afc [0x41, 0x8D, 0x47, 0x01] (fun s => s.RIP = 0x126afc) (leaR32Effect 0x126afc 4 0 (.base 15 (.d8 0x1)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (leaR32Effect_footprint 0x126afc 4 0 (.base 15 (.d8 0x1))).toInstrSpec (lea_r32_rex_effect_step 0x126afc 0x41 (by decide) 0 (.base 15 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126b00 [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x126b00) (shlR64Effect 0x126b00 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x126b00 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x126b00 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126b04 [0x48, 0x83, 0xC8, 0x03] (fun s => s.RIP = 0x126b04) (orR64Imm8Effect 0x126b04 0 0x3)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x126b04 0 0x3).toInstrSpec (or_r64_imm8_effect_step 0x126b04 0x48 0xc8 0x3 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (7, 7), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b00) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (7, 7), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b04) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (7, 7), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b08) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l126afc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126afc :=
  Rest.liftedBlock (rest_l126afc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126afc x hx)

theorem rest_l126b08 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126b08 bytes_l126b08) (entryMap (live .l126b08))
      4 0x126b08 bytes_l126b08 b_l126b08 := by
  have f0 : InstrSpec 0x126b08 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126b08) (movR32Imm32Effect 0x126b08 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x126b08 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x126b08 0xba (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x126b0d [0x31, 0xFF] (fun s => s.RIP = 0x126b0d) (xorR32R32Effect 0x126b0d 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x126b0d 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x126b0d 0xff (by decide)) pre_rip
  have f2 : InstrSpec 0x126b0f [0x44, 0x89, 0xF9] (fun s => s.RIP = 0x126b0f) (movR32R32Effect 0x126b0f 3 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x126b0f 3 1 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x126b0f 0x44 0xf9 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x126b12 [0x44, 0x89, 0xFE] (fun s => s.RIP = 0x126b12) (movR32R32Effect 0x126b12 3 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x126b12 3 6 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x126b12 0x44 0xfe (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (7, 7), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b0d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (7, 55), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b0f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 53), (3, 3), (4, 4), (7, 55), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b12) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 57), (2, 53), (3, 3), (4, 4), (6, 59), (7, 55), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b15) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l126b08 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126b08 :=
  Rest.liftedBlock (rest_l126b08 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126b08 x hx)

theorem rest_l126b15 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126b15 bytes_l126b15) (entryMap (live .l126b15))
      19 0x126b15 bytes_l126b15 b_l126b15 := by
  have f0 : InstrSpec 0x126b15 [0x89, 0xF6] (fun s => s.RIP = 0x126b15) (movR32R32Effect 0x126b15 2 6 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x126b15 2 6 6).toInstrSpec (mov_r32_r32_effect_step 0x126b15 0xf6 (by decide)) pre_rip
  have f1 : InstrSpec 0x126b17 [0x48, 0x09, 0xFE] (fun s => s.RIP = 0x126b17) (orR64R64Effect 0x126b17 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x126b17 6 7).toInstrSpec (or_r64_r64_effect_step 0x126b17 0x48 0xfe (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126b1a [0x48, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x126b1a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126b1a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126b1a 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126b1a 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x126b1a 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126b1f [0x48, 0x89, 0x7C, 0x24, 0x40] (StorePre 0x126b1f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x126b1f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126b1f 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126b1f 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x126b1f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x126b24 [0x4C, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x126b24 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126b24 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126b24 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x126b24 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x126b24 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x126b29 [0x4C, 0x89, 0x44, 0x24, 0x38] (StorePre 0x126b29 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x126b29 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126b29 8 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126b29 8 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x126b29 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x126b2e [0x4C, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x126b2e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126b2e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126b2e 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x126b2e 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x126b2e 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x126b33 [0x4C, 0x8B, 0x54, 0x24, 0x10] (LoadPre 0x126b33 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126b33 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126b33 10 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x126b33 10 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x126b33 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x126b38 [0x4C, 0x89, 0x54, 0x24, 0x30] (StorePre 0x126b38 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x126b38 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126b38 10 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126b38 10 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x126b38 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x126b3d [0x4C, 0x89, 0x4C, 0x24, 0x28] (StorePre 0x126b3d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126b3d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126b3d 9 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126b3d 9 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x126b3d 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x126b42 [0x48, 0x89, 0x7B, 0x38] (StorePre 0x126b42 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x126b42 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b42 7 (.base 3 (.d8 0x38)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126b42 7 (.base 3 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x126b42 0x48 (by decide) 7 (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x126b46 [0x4C, 0x89, 0x43, 0x30] (StorePre 0x126b46 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x126b46 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b46 8 (.base 3 (.d8 0x30)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126b46 8 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x126b46 0x4c (by decide) 0 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x126b4a [0x4C, 0x89, 0x53, 0x28] (StorePre 0x126b4a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x126b4a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b4a 10 (.base 3 (.d8 0x28)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126b4a 10 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x126b4a 0x4c (by decide) 2 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x126b4e [0x4C, 0x89, 0x4B, 0x20] (StorePre 0x126b4e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x126b4e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b4e 9 (.base 3 (.d8 0x20)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126b4e 9 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x126b4e 0x4c (by decide) 1 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x126b52 [0x89, 0x53, 0x08] (StorePre 0x126b52 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x126b52 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126b52 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126b52 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x126b52 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x126b55 [0x89, 0x4B, 0x0C] (StorePre 0x126b55 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x126b55 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126b55 1 (.base 3 (.d8 0xc)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126b55 1 (.base 3 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x126b55 1 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x126b58 [0x48, 0x89, 0x43, 0x10] (StorePre 0x126b58 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x126b58 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b58 0 (.base 3 (.d8 0x10)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126b58 0 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x126b58 0x48 (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x126b5c [0x48, 0x89, 0x73, 0x18] (StorePre 0x126b5c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x126b5c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b5c 6 (.base 3 (.d8 0x18)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126b5c 6 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x126b5c 0x48 (by decide) 6 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x126b60 [0x48, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00] (StorePre 0x126b60 7 (fun s => AddrMode.addr (.base 3 .none) s (0x126b60 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x126b60 (.base 3 .none) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x126b60 (.base 3 .none) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x126b60 0x48 (by decide) (.base 3 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (7, 7), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b17) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 7), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b1a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b1f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b24) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 60), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b29) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 60), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b2e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 60), (9, 63), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b33) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 60), (9, 63), (10, 65), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b38) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 60), (9, 63), (10, 65), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b3d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 60), (9, 63), (10, 65), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b42) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 60), (9, 63), (10, 65), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b46) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 60), (9, 63), (10, 65), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b4a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 60), (9, 63), (10, 65), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b4e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 60), (9, 63), (10, 65), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b52) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 60), (9, 63), (10, 65), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b55) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 60), (9, 63), (10, 65), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b58) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 60), (9, 63), (10, 65), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b5c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 60), (9, 63), (10, 65), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b60) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 60), (9, 63), (10, 65), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b67) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 78) (by decide) rfl

theorem block_l126b15 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126b15 :=
  Rest.liftedBlock (rest_l126b15 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126b15 x hx)

theorem rest_l126b67 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126b67 bytes_l126b67) (entryMap (live .l126b67))
      9 0x126b67 bytes_l126b67 b_l126b67 := by
  have f0 : InstrSpec 0x126b67 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x126b67) (movR64R64Effect 0x126b67 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x126b67 0 3).toInstrSpec (mov_r64_r64_effect_step 0x126b67 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126b6a [0x48, 0x81, 0xC4, 0xD8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126b6a) (addR64Imm32Effect 0x126b6a 4 0xd8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x126b6a 4 0xd8).toInstrSpec (add_r64_imm32_effect_step 0x126b6a 0x48 0xc4 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126b71 [0x5B] (PopPre 0x126b71) (popR64Effect 0x126b71 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126b71 1 3).toInstrSpec (pop_r64_effect_step 0x126b71 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x126b72 [0x41, 0x5C] (PopPre 0x126b72) (popR64Effect 0x126b72 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126b72 2 12).toInstrSpec (pop_r64_rex_effect_step 0x126b72 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x126b74 [0x41, 0x5D] (PopPre 0x126b74) (popR64Effect 0x126b74 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126b74 2 13).toInstrSpec (pop_r64_rex_effect_step 0x126b74 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x126b76 [0x41, 0x5E] (PopPre 0x126b76) (popR64Effect 0x126b76 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126b76 2 14).toInstrSpec (pop_r64_rex_effect_step 0x126b76 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x126b78 [0x41, 0x5F] (PopPre 0x126b78) (popR64Effect 0x126b78 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126b78 2 15).toInstrSpec (pop_r64_rex_effect_step 0x126b78 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x126b7a [0x5D] (PopPre 0x126b7a) (popR64Effect 0x126b7a 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126b7a 1 5).toInstrSpec (pop_r64_effect_step 0x126b7a 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x126b7b [0xC3] (RetPre 0x126b7b) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x126b7b).toInstrSpec (ret_effect_step 0x126b7b) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b6a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b71) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b72) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b74) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b76) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b78) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b7a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b7b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l126b67 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126b67 :=
  Rest.liftedBlock (rest_l126b67 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126b67 x hx)

theorem rest_l126b7c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126b7c bytes_l126b7c) (entryMap (live .l126b7c))
      10 0x126b7c bytes_l126b7c b_l126b7c := by
  have f0 : InstrSpec 0x126b7c [0x41, 0x89, 0x6E, 0x18] (StorePre 0x126b7c 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126b7c + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126b7c 5 (.base 14 (.d8 0x18)))
      [.gpr 5, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x126b7c 5 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x126b7c 0x41 (by decide) 5 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x126b80 [0x48, 0x8D, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126b80) (leaR64Effect 0x126b80 2 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x126b80 2 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (lea_r64_effect_step 0x126b80 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126b88 [0x49, 0x8B, 0x45, 0x00] (LoadPre 0x126b88 (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x126b88 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126b88 0 (.base 13 (.d8 0x0)))
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126b88 0 (.base 13 (.d8 0x0))).toInstrSpec (mov_r64_m64_effect_step 0x126b88 0x49 (by decide) 0 (.base 13 (.d8 0x0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126b8c [0x49, 0x8B, 0x4D, 0x08] (LoadPre 0x126b8c (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x126b8c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126b8c 1 (.base 13 (.d8 0x8)))
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x126b8c 1 (.base 13 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x126b8c 0x49 (by decide) 1 (.base 13 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x126b90 [0x48, 0x89, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x126b90 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x126b90 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126b90 1 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126b90 1 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x126b90 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x126b98 [0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x126b98 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x126b98 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126b98 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126b98 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x126b98 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x126ba0 [0x4C, 0x89, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x126ba0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x126ba0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126ba0 14 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126ba0 14 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x126ba0 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x126ba8 [0x48, 0x8D, 0x7C, 0x24, 0x48] (fun s => s.RIP = 0x126ba8) (leaR64Effect 0x126ba8 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x126ba8 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x126ba8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x126bad [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x126bad) (movR64R64Effect 0x126bad 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x126bad 6 14).toInstrSpec (mov_r64_r64_effect_step 0x126bad 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x126bb0 [0xE8, 0x2B, 0xE2, 0xFF, 0xFF] (PushPre 0x126bb0 5) (callEffect (fun _ => 0x124de0) 0x126bb5)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x126bb0 0x124de0 0x126bb5).toInstrSpec (call_rel32_effect_step 0x126bb0 0xffffe22b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b80) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b88) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b8c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b90) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126b98) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ba0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ba8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126bad) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (6, 64), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126bb0) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 66), (5, 5), (6, 64), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124de0) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l126b7c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126b7c :=
  Rest.liftedBlock (rest_l126b7c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126b7c x hx)

theorem rest_l126bb5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126bb5 bytes_l126bb5) (entryMap (live .l126bb5))
      16 0x126bb5 bytes_l126bb5 b_l126bb5 := by
  have f0 : InstrSpec 0x126bb5 [0x41, 0x8B, 0x76, 0x18] (LoadPre 0x126bb5 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126bb5 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126bb5 6 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR32M32Effect_footprint 0x126bb5 6 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x126bb5 0x41 (by decide) 6 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126bb9 [0x41, 0x8B, 0x4E, 0x1C] (LoadPre 0x126bb9 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x126bb9 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126bb9 1 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x126bb9 1 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x126bb9 0x41 (by decide) 1 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126bbd [0x29, 0xCE] (fun s => s.RIP = 0x126bbd) (subR32R32Effect 0x126bbd 2 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (subR32R32Effect_footprint 0x126bbd 2 6 1).toInstrSpec (sub_r32_r32_effect_step 0x126bbd 0xce (by decide)) pre_rip
  have f3 : InstrSpec 0x126bbf [0x0F, 0x96, 0xC0] (fun s => s.RIP = 0x126bbf) (atFlags (condHolds 6) (setccR8Effect 0x126bbf 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x126bbf 3 0 6).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x126bbf 6 0xc0 (by decide) (by decide) c)) pre_rip
  have f4 : InstrSpec 0x126bc2 [0x48, 0x8B, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x126bc2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x126bc2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126bc2 2 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x126bc2 2 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x126bc2 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x126bca [0x49, 0x89, 0x16] (StorePre 0x126bca 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126bca + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126bca 2 (.base 14 .none))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126bca 2 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x126bca 0x49 (by decide) 2 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x126bcd [0x4D, 0x89, 0x66, 0x08] (StorePre 0x126bcd 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126bcd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126bcd 12 (.base 14 (.d8 0x8)))
      [.gpr 12, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126bcd 12 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x126bcd 0x4d (by decide) 4 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x126bd1 [0x45, 0x89, 0x7E, 0x18] (StorePre 0x126bd1 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126bd1 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126bd1 15 (.base 14 (.d8 0x18)))
      [.gpr 15, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x126bd1 15 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x126bd1 0x45 (by decide) 7 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x126bd5 [0x49, 0x8B, 0x56, 0x10] (LoadPre 0x126bd5 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126bd5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126bd5 2 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x126bd5 2 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x126bd5 0x49 (by decide) 2 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x126bd9 [0x48, 0x83, 0xFA, 0x01] (fun s => s.RIP = 0x126bd9) (cmpR64Imm8Effect 0x126bd9 2 0x1)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x126bd9 2 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x126bd9 0x48 0xfa 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x126bdd [0x48, 0x83, 0xD2, 0xFF] (fun s => s.RIP = 0x126bdd) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x126bdd 2 0xff))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x126bdd 2 0xff).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x126bdd 0x48 0xd2 0xff c (by decide) (by decide) (by decide))) pre_rip
  have f11 : InstrSpec 0x126be1 [0x49, 0x89, 0x56, 0x10] (StorePre 0x126be1 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126be1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126be1 2 (.base 14 (.d8 0x10)))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126be1 2 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x126be1 0x49 (by decide) 2 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x126be5 [0x48, 0x8B, 0x7C, 0x24, 0x48] (LoadPre 0x126be5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126be5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126be5 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126be5 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x126be5 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x126bea [0x89, 0xFA] (fun s => s.RIP = 0x126bea) (movR32R32Effect 0x126bea 2 2 7)
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x126bea 2 2 7).toInstrSpec (mov_r32_r32_effect_step 0x126bea 0xfa (by decide)) pre_rip
  have f14 : InstrSpec 0x126bec [0x08, 0xC2] (fun s => s.RIP = 0x126bec) (orR8R8Effect 0x126bec 2 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (orR8R8Effect_footprint 0x126bec 2 2 0).toInstrSpec (or_r8_r8_effect_step 0x126bec 0xc2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126bb9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126bbd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 59) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126bbf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 55), (3, 3), (4, 4), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126bc2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 55), (2, 63), (3, 3), (4, 4), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126bca) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 61), (1, 55), (2, 63), (3, 3), (4, 4), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126bcd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 55), (2, 63), (3, 3), (4, 4), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126bd1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 61), (1, 55), (2, 63), (3, 3), (4, 4), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126bd5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 61), (1, 55), (2, 68), (3, 3), (4, 4), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126bd9) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 61), (1, 55), (2, 68), (3, 3), (4, 4), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126bdd) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 61), (1, 55), (2, 72), (3, 3), (4, 4), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126be1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 61), (1, 55), (2, 72), (3, 3), (4, 4), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126be5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 61), (1, 55), (2, 72), (3, 3), (4, 4), (6, 57), (7, 75), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126bea) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 61), (1, 55), (2, 77), (3, 3), (4, 4), (6, 57), (7, 75), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126bec) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 61), (1, 55), (3, 3), (4, 4), (6, 57), (7, 75), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126bee) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 81) (jcc_rel32_effect_step 0x126bee 4 0x100) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126bb5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126bb5 :=
  Rest.liftedBlock (rest_l126bb5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126bb5 x hx)

theorem rest_l126bf4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126bf4 bytes_l126bf4) (entryMap (live .l126bf4))
      20 0x126bf4 bytes_l126bf4 b_l126bf4 := by
  have f0 : InstrSpec 0x126bf4 [0x8B, 0x54, 0x24, 0x50] (LoadPre 0x126bf4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126bf4 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126bf4 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x126bf4 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r32_m32_low_effect_step 0x126bf4 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126bf8 [0x8B, 0x4C, 0x24, 0x54] (LoadPre 0x126bf8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x126bf8 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126bf8 1 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x126bf8 1 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_r32_m32_low_effect_step 0x126bf8 1 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126bfc [0x48, 0x8B, 0x44, 0x24, 0x58] (LoadPre 0x126bfc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126bfc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126bfc 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126bfc 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x126bfc 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126c01 [0x48, 0x8B, 0x74, 0x24, 0x60] (LoadPre 0x126c01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126c01 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c01 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x126c01 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x126c01 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x126c06 [0x4C, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x126c06 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x126c06 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c06 8 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x126c06 8 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x126c06 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x126c0b [0x4C, 0x89, 0x44, 0x24, 0x08] (StorePre 0x126c0b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126c0b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c0b 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126c0b 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x126c0b 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x126c10 [0x4C, 0x8B, 0x44, 0x24, 0x70] (LoadPre 0x126c10 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x126c10 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c10 8 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x126c10 8 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x126c10 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x126c15 [0x4C, 0x89, 0x44, 0x24, 0x10] (StorePre 0x126c15 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126c15 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c15 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126c15 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x126c15 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x126c1a [0x4C, 0x8B, 0x44, 0x24, 0x78] (LoadPre 0x126c1a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126c1a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c1a 8 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x126c1a 8 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x126c1a 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x126c1f [0x4C, 0x89, 0x44, 0x24, 0x18] (StorePre 0x126c1f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126c1f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c1f 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126c1f 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x126c1f 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x126c24 [0x4C, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x126c24 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x126c24 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c24 8 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x126c24 8 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x126c24 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x126c2c [0x4C, 0x89, 0x44, 0x24, 0x20] (StorePre 0x126c2c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126c2c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c2c 8 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126c2c 8 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x126c2c 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x126c31 [0x4C, 0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x126c31 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x126c31 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c31 8 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x126c31 8 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x126c31 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x126c39 [0x4C, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x126c39 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x126c39 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126c39 8 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126c39 8 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x126c39 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x126c41 [0x4C, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x126c41 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x126c41 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c41 8 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x126c41 8 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x126c41 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x126c49 [0x4C, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x126c49 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x126c49 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126c49 8 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126c49 8 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x126c49 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x126c51 [0x4C, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x126c51 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x126c51 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c51 8 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x126c51 8 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x126c51 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x126c59 [0x4C, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x126c59 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x126c59 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126c59 8 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126c59 8 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x126c59 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x126c61 [0x48, 0x85, 0xFF] (fun s => s.RIP = 0x126c61) (testR64R64Effect 0x126c61 7 7)
      [.gpr 7, .gpr 7] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x126c61 7 7).toInstrSpec (test_r64_r64_effect_step 0x126c61 0x48 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126bf8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126bfc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c01) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c06) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 61), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c0b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 61), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c10) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 64), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c15) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 64), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c1a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c1f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c24) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 70), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c2c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 70), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c31) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 73), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c39) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 73), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c41) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 76), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c49) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 76), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c51) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 79), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c59) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 79), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c61) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f18 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 79), (9, 9), (10, 10), (11, 11), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c64) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 84) (jcc_rel32_effect_step 0x126c64 5 0xfffffe6f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126bf4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126bf4 :=
  Rest.liftedBlock (rest_l126bf4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126bf4 x hx)

theorem rest_l126c6a_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x126c6a bytes_l126c6a) [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 80), (8, 82), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]
      8 0x126cd2 bytes_l126c6a_1 b_l126c6a_1 := by
  have f20 : InstrSpec 0x126cd2 [0x4C, 0x89, 0x43, 0x28] (StorePre 0x126cd2 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x126cd2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cd2 8 (.base 3 (.d8 0x28)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126cd2 8 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x126cd2 0x4c (by decide) 0 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x126cd6 [0x48, 0x89, 0x7B, 0x20] (StorePre 0x126cd6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x126cd6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cd6 7 (.base 3 (.d8 0x20)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126cd6 7 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x126cd6 0x48 (by decide) 7 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x126cda [0x89, 0x53, 0x08] (StorePre 0x126cda 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x126cda + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126cda 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126cda 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x126cda 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x126cdd [0x89, 0x4B, 0x0C] (StorePre 0x126cdd 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x126cdd + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126cdd 1 (.base 3 (.d8 0xc)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126cdd 1 (.base 3 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x126cdd 1 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x126ce0 [0x48, 0x89, 0x43, 0x10] (StorePre 0x126ce0 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x126ce0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126ce0 0 (.base 3 (.d8 0x10)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126ce0 0 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x126ce0 0x48 (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x126ce4 [0x48, 0x89, 0x73, 0x18] (StorePre 0x126ce4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x126ce4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126ce4 6 (.base 3 (.d8 0x18)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126ce4 6 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x126ce4 0x48 (by decide) 6 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x126ce8 [0x48, 0xC7, 0x03, 0x00, 0x00, 0x00, 0x00] (StorePre 0x126ce8 7 (fun s => AddrMode.addr (.base 3 .none) s (0x126ce8 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x126ce8 (.base 3 .none) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x126ce8 (.base 3 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x126ce8 0x48 (by decide) (.base 3 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 80), (8, 82), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126cd6) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 80), (8, 82), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126cda) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 80), (8, 82), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126cdd) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 80), (8, 82), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ce0) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 80), (8, 82), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ce4) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 80), (8, 82), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ce8) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 80), (8, 82), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126cef) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 91) (jmp_rel32_effect_step 0x126cef 0xfffffe73 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l126c6a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126c6a bytes_l126c6a) (entryMap (live .l126c6a))
      28 0x126c6a bytes_l126c6a b_l126c6a := by
  have f0 : InstrSpec 0x126c6a [0x48, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x126c6a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126c6a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c6a 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126c6a 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x126c6a 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126c6f [0x48, 0x89, 0x7C, 0x24, 0x40] (StorePre 0x126c6f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x126c6f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c6f 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126c6f 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x126c6f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x126c74 [0x48, 0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x126c74 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126c74 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c74 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126c74 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x126c74 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126c79 [0x48, 0x89, 0x7C, 0x24, 0x38] (StorePre 0x126c79 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x126c79 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c79 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126c79 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x126c79 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x126c7e [0x48, 0x8B, 0x7C, 0x24, 0x08] (LoadPre 0x126c7e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126c7e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c7e 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126c7e 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x126c7e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x126c83 [0x4C, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x126c83 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126c83 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c83 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x126c83 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x126c83 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x126c88 [0x4C, 0x89, 0x44, 0x24, 0x30] (StorePre 0x126c88 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x126c88 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c88 8 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126c88 8 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x126c88 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x126c8d [0x48, 0x89, 0x7C, 0x24, 0x28] (StorePre 0x126c8d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126c8d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c8d 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126c8d 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x126c8d 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x126c92 [0x48, 0x8B, 0xBC, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x126c92 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x126c92 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c92 7 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126c92 7 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x126c92 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x126c9a [0x48, 0x89, 0x7B, 0x50] (StorePre 0x126c9a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x126c9a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126c9a 7 (.base 3 (.d8 0x50)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126c9a 7 (.base 3 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x126c9a 0x48 (by decide) 7 (.base 3 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x126c9e [0x48, 0x8B, 0xBC, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x126c9e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x126c9e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c9e 7 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126c9e 7 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x126c9e 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x126ca6 [0x4C, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x126ca6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x126ca6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126ca6 8 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x126ca6 8 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x126ca6 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x126cae [0x4C, 0x89, 0x43, 0x48] (StorePre 0x126cae 4 (fun s => AddrMode.addr (.base 3 (.d8 0x48)) s (0x126cae + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cae 8 (.base 3 (.d8 0x48)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126cae 8 (.base 3 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x126cae 0x4c (by decide) 0 (.base 3 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x126cb2 [0x48, 0x89, 0x7B, 0x40] (StorePre 0x126cb2 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x126cb2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cb2 7 (.base 3 (.d8 0x40)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126cb2 7 (.base 3 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x126cb2 0x48 (by decide) 7 (.base 3 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x126cb6 [0x48, 0x8B, 0x7C, 0x24, 0x40] (LoadPre 0x126cb6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x126cb6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126cb6 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126cb6 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x126cb6 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x126cbb [0x48, 0x89, 0x7B, 0x38] (StorePre 0x126cbb 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x126cbb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cbb 7 (.base 3 (.d8 0x38)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126cbb 7 (.base 3 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x126cbb 0x48 (by decide) 7 (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x126cbf [0x48, 0x8B, 0x7C, 0x24, 0x38] (LoadPre 0x126cbf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x126cbf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126cbf 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126cbf 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x126cbf 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x126cc4 [0x48, 0x89, 0x7B, 0x30] (StorePre 0x126cc4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x126cc4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cc4 7 (.base 3 (.d8 0x30)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126cc4 7 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x126cc4 0x48 (by decide) 7 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x126cc8 [0x48, 0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x126cc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126cc8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126cc8 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126cc8 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x126cc8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x126ccd [0x4C, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x126ccd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x126ccd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ccd 8 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x126ccd 8 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x126ccd 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c6f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c74) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 56), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c79) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 56), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c7e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c83) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 59), (8, 61), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c88) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 59), (8, 61), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c8d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 59), (8, 61), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c92) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 65), (8, 61), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c9a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 65), (8, 61), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126c9e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 68), (8, 61), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ca6) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 68), (8, 70), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126cae) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 68), (8, 70), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126cb2) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 68), (8, 70), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126cb6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 74), (8, 70), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126cbb) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 74), (8, 70), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126cbf) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 77), (8, 70), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126cc4) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 77), (8, 70), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126cc8) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 80), (8, 70), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ccd) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 80), (8, 82), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126cd2) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l126c6a_1 code

theorem block_l126c6a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126c6a :=
  Rest.liftedBlock (rest_l126c6a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126c6a x hx)

theorem rest_l126cf4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126cf4 bytes_l126cf4) (entryMap (live .l126cf4))
      7 0x126cf4 bytes_l126cf4 b_l126cf4 := by
  have f0 : InstrSpec 0x126cf4 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x126cf4 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x126cf4 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x126cf4 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x126cf4 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x126cf4 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x126cf9 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x126cf9) (movR64R64Effect 0x126cf9 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x126cf9 0 1).toInstrSpec (mov_r64_r64_effect_step 0x126cf9 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126cfc [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x126cfc) (shlR64Effect 0x126cfc 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x126cfc 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x126cfc 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x126d00 [0x48, 0x83, 0xC8, 0x13] (fun s => s.RIP = 0x126d00) (orR64Imm8Effect 0x126d00 0 0x13)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x126d00 0 0x13).toInstrSpec (or_r64_imm8_effect_step 0x126d00 0x48 0xc8 0x13 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x126d04 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126d04) (movR32Imm32Effect 0x126d04 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x126d04 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x126d04 0xba (by decide) 0x1) pre_rip
  have f5 : InstrSpec 0x126d09 [0x31, 0xFF] (fun s => s.RIP = 0x126d09) (xorR32R32Effect 0x126d09 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x126d09 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x126d09 0xff (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126cf9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126cfc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d00) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d04) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 58), (1, 1), (2, 60), (3, 3), (4, 4), (6, 6), (7, 7), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d09) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 58), (1, 1), (2, 60), (3, 3), (4, 4), (6, 6), (7, 62), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d0b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 64) (jmp_rel32_effect_step 0x126d0b 0xfffffe05 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126cf4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126cf4 :=
  Rest.liftedBlock (rest_l126cf4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126cf4 x hx)

theorem rest_l126d10 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126d10 bytes_l126d10) (entryMap (live .l126d10))
      4 0x126d10 bytes_l126d10 b_l126d10 := by
  have f0 : InstrSpec 0x126d10 [0x31, 0xD2] (fun s => s.RIP = 0x126d10) (xorR32R32Effect 0x126d10 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x126d10 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x126d10 0xd2 (by decide)) pre_rip
  have f1 : InstrSpec 0x126d12 [0xB8, 0x0C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126d12) (movR32Imm32Effect 0x126d12 5 0 0xc)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x126d12 5 0 0xc).toInstrSpec (mov_r32_imm32_effect_step 0x126d12 0xb8 (by decide) 0xc) pre_rip
  have f2 : InstrSpec 0x126d17 [0x31, 0xFF] (fun s => s.RIP = 0x126d17) (xorR32R32Effect 0x126d17 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x126d17 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x126d17 0xff (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d12) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d17) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 57), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d19) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x126d19 0xfffffdf7 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126d10 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126d10 :=
  Rest.liftedBlock (rest_l126d10 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126d10 x hx)

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

theorem_by block_l126a30_eval :
    program.runBlock (dialect code) ⟨.l126a30, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126a54_eval :
    program.runBlock (dialect code) ⟨.l126a54, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126a78_eval :
    program.runBlock (dialect code) ⟨.l126a78, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126a81_eval :
    program.runBlock (dialect code) ⟨.l126a81, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126a9c_eval :
    program.runBlock (dialect code) ⟨.l126a9c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126aa3_eval :
    program.runBlock (dialect code) ⟨.l126aa3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126ad9_eval :
    program.runBlock (dialect code) ⟨.l126ad9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126ae8_eval :
    program.runBlock (dialect code) ⟨.l126ae8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126afc_eval :
    program.runBlock (dialect code) ⟨.l126afc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126b08_eval :
    program.runBlock (dialect code) ⟨.l126b08, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126b15_eval :
    program.runBlock (dialect code) ⟨.l126b15, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126b67_eval :
    program.runBlock (dialect code) ⟨.l126b67, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126b7c_eval :
    program.runBlock (dialect code) ⟨.l126b7c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126bb5_eval :
    program.runBlock (dialect code) ⟨.l126bb5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126bf4_eval :
    program.runBlock (dialect code) ⟨.l126bf4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126c6a_eval :
    program.runBlock (dialect code) ⟨.l126c6a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126cf4_eval :
    program.runBlock (dialect code) ⟨.l126cf4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126d10_eval :
    program.runBlock (dialect code) ⟨.l126d10, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Generate.LIR
