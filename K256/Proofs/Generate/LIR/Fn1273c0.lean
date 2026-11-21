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

theorem rest_l1273c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1273c0 bytes_l1273c0) (entryMap (live .l1273c0))
      12 0x1273c0 bytes_l1273c0 b_l1273c0 := by
  have f0 : InstrSpec 0x1273c0 [0x55] (PushPre 0x1273c0 1) (pushR64Effect 0x1273c0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1273c0 1 5).toInstrSpec (push_r64_effect_step 0x1273c0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1273c1 [0x41, 0x57] (PushPre 0x1273c1 2) (pushR64Effect 0x1273c1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1273c1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1273c1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1273c3 [0x41, 0x56] (PushPre 0x1273c3 2) (pushR64Effect 0x1273c3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1273c3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1273c3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1273c5 [0x41, 0x55] (PushPre 0x1273c5 2) (pushR64Effect 0x1273c5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1273c5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1273c5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1273c7 [0x41, 0x54] (PushPre 0x1273c7 2) (pushR64Effect 0x1273c7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1273c7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1273c7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1273c9 [0x53] (PushPre 0x1273c9 1) (pushR64Effect 0x1273c9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1273c9 1 3).toInstrSpec (push_r64_effect_step 0x1273c9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1273ca [0x48, 0x83, 0xEC, 0x78] (fun s => s.RIP = 0x1273ca) (subR64Imm8Effect 0x1273ca 4 0x78)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1273ca 4 0x78).toInstrSpec (sub_r64_imm8_effect_step 0x1273ca 0x48 0xec 0x78 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1273ce [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x1273ce) (movR64R64Effect 0x1273ce 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1273ce 3 7).toInstrSpec (mov_r64_r64_effect_step 0x1273ce 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1273d1 [0x44, 0x8B, 0x7E, 0x1C] (LoadPre 0x1273d1 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x1273d1 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1273d1 15 (.base 6 (.d8 0x1c)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x1273d1 15 (.base 6 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x1273d1 0x44 (by decide) 7 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1273d5 [0x8B, 0x6A, 0x08] (LoadPre 0x1273d5 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1273d5 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1273d5 5 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR32M32LowEffect_footprint 0x1273d5 5 (.base 2 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x1273d5 5 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1273d8 [0x44, 0x01, 0xFD] (fun s => s.RIP = 0x1273d8) (addR32R32Effect 0x1273d8 3 5 15)
      [.gpr 5, .gpr 15] [] [.reg 5, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1273d8 3 5 15).toInstrSpec (add_r32_r32_rex_effect_step 0x1273d8 0x44 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273c3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273c5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273c7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273c9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273ca) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273ce) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273d1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273d5) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273d8) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273db) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 76) (jcc_rel32_effect_step 0x1273db 2 0x1f3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1273c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1273c0 :=
  Rest.liftedBlock (rest_l1273c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1273c0 x hx)

theorem rest_l1273e1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1273e1 bytes_l1273e1) (entryMap (live .l1273e1))
      9 0x1273e1 bytes_l1273e1 b_l1273e1 := by
  have f0 : InstrSpec 0x1273e1 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x1273e1) (movR64R64Effect 0x1273e1 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1273e1 13 2).toInstrSpec (mov_r64_r64_effect_step 0x1273e1 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1273e4 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x1273e4) (movR64R64Effect 0x1273e4 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1273e4 14 6).toInstrSpec (mov_r64_r64_effect_step 0x1273e4 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1273e7 [0x48, 0x8B, 0x36] (LoadPre 0x1273e7 (fun s => AddrMode.addr (.base 6 .none) s (0x1273e7 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1273e7 6 (.base 6 .none))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1273e7 6 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1273e7 0x48 (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1273ea [0x4D, 0x8B, 0x66, 0x08] (LoadPre 0x1273ea (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1273ea + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1273ea 12 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x1273ea 12 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1273ea 0x4d (by decide) 4 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1273ee [0x48, 0x8D, 0x7C, 0x24, 0x20] (fun s => s.RIP = 0x1273ee) (leaR64Effect 0x1273ee 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1273ee 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x1273ee 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1273f3 [0x48, 0x89, 0x74, 0x24, 0x58] (StorePre 0x1273f3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1273f3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1273f3 6 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1273f3 6 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x1273f3 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1273f8 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x1273f8) (movR64R64Effect 0x1273f8 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1273f8 2 12).toInstrSpec (mov_r64_r64_effect_step 0x1273f8 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1273fb [0x89, 0xE9] (fun s => s.RIP = 0x1273fb) (movR32R32Effect 0x1273fb 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1273fb 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x1273fb 0xe9 (by decide)) pre_rip
  have f8 : InstrSpec 0x1273fd [0xE8, 0x4E, 0x08, 0x00, 0x00] (PushPre 0x1273fd 5) (callEffect (fun _ => 0x127c50) 0x127402)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1273fd 0x127c50 0x127402).toInstrSpec (call_rel32_effect_step 0x1273fd 0x84e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273e4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273e7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273ea) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273ee) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273f3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273f8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 64), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273fb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273fd) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 68), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c50) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 70) (by decide) (by decide) rfl rfl

theorem block_l1273e1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1273e1 :=
  Rest.liftedBlock (rest_l1273e1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1273e1 x hx)

theorem rest_l127402 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127402 bytes_l127402) (entryMap (live .l127402))
      3 0x127402 bytes_l127402 b_l127402 := by
  have f0 : InstrSpec 0x127402 [0x8B, 0x54, 0x24, 0x20] (LoadPre 0x127402 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x127402 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x127402 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x127402 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r32_m32_low_effect_step 0x127402 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127406 [0x83, 0xFA, 0x02] (fun s => s.RIP = 0x127406) (cmpR32Imm8Effect 0x127406 3 2 0x2)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x127406 3 2 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x127406 0xfa 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127406) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127409) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x127409 5 0x22) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127402 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127402 :=
  Rest.liftedBlock (rest_l127402 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127402 x hx)

theorem rest_l12740b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12740b bytes_l12740b) (entryMap (live .l12740b))
      7 0x12740b bytes_l12740b b_l12740b := by
  have f0 : InstrSpec 0x12740b [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x12740b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x12740b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12740b 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12740b 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x12740b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127410 [0x48, 0x8B, 0x4C, 0x24, 0x30] (LoadPre 0x127410 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x127410 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127410 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x127410 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x127410 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x127415 [0x49, 0x89, 0x06] (StorePre 0x127415 3 (fun s => AddrMode.addr (.base 14 .none) s (0x127415 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x127415 0 (.base 14 .none))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x127415 0 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x127415 0x49 (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x127418 [0x49, 0x89, 0x4E, 0x08] (StorePre 0x127418 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x127418 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127418 1 (.base 14 (.d8 0x8)))
      [.gpr 1, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x127418 1 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x127418 0x49 (by decide) 1 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12741c [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x12741c (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x12741c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12741c 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12741c 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x12741c 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x127420 [0x48, 0x83, 0xF8, 0x3F] (fun s => s.RIP = 0x127420) (cmpR64Imm8Effect 0x127420 0 0x3f)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x127420 0 0x3f).toInstrSpec (cmp_r64_imm8_effect_step 0x127420 0x48 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127410) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127415) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127418) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12741c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127420) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127424) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x127424 6 0x50) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12740b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12740b :=
  Rest.liftedBlock (rest_l12740b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12740b x hx)

theorem rest_l127426 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127426 bytes_l127426) (entryMap (live .l127426))
      2 0x127426 bytes_l127426 b_l127426 := by
  have f0 : InstrSpec 0x127426 [0xB8, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127426) (movR32Imm32Effect 0x127426 5 0 0x6)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x127426 5 0 0x6).toInstrSpec (mov_r32_imm32_effect_step 0x127426 0xb8 (by decide) 0x6) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (7, 7), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12742b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x12742b 0x65 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l127426 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127426 :=
  Rest.liftedBlock (rest_l127426 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127426 x hx)

theorem rest_l12742d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12742d bytes_l12742d) (entryMap (live .l12742d))
      11 0x12742d bytes_l12742d b_l12742d := by
  have f0 : InstrSpec 0x12742d [0x8B, 0x4C, 0x24, 0x24] (LoadPre 0x12742d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x12742d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12742d 1 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x12742d 1 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r32_m32_low_effect_step 0x12742d 1 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127431 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x127431 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x127431 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127431 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x127431 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x127431 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x127436 [0x4C, 0x8B, 0x7C, 0x24, 0x30] (LoadPre 0x127436 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x127436 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127436 15 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x127436 15 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x127436 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12743b [0x48, 0x8B, 0x74, 0x24, 0x38] (LoadPre 0x12743b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x12743b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12743b 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12743b 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x12743b 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x127440 [0x48, 0x89, 0x34, 0x24] (StorePre 0x127440 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x127440 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127440 6 (.sib 4 none 0 .none))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x127440 6 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x127440 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x127444 [0x48, 0x8B, 0x74, 0x24, 0x40] (LoadPre 0x127444 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x127444 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127444 6 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x127444 6 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x127444 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x127449 [0x48, 0x89, 0x74, 0x24, 0x08] (StorePre 0x127449 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x127449 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127449 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x127449 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x127449 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x12744e [0x48, 0x8B, 0x74, 0x24, 0x48] (LoadPre 0x12744e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x12744e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12744e 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12744e 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x12744e 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x127453 [0x48, 0x89, 0x74, 0x24, 0x10] (StorePre 0x127453 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x127453 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127453 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x127453 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x127453 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x127458 [0x48, 0x8B, 0x74, 0x24, 0x50] (LoadPre 0x127458 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x127458 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127458 6 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x127458 6 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x127458 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x12745d [0x48, 0x89, 0x74, 0x24, 0x18] (StorePre 0x12745d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12745d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12745d 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12745d 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x12745d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127431) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127436) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12743b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 59), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127440) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 59), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127444) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 62), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127449) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 62), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12744e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 65), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127453) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 65), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127458) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 68), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12745d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 68), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127462) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 71) (by decide) rfl

theorem block_l12742d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12742d :=
  Rest.liftedBlock (rest_l12742d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12742d x hx)

theorem rest_l127462 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127462 bytes_l127462) (entryMap (live .l127462))
      5 0x127462 bytes_l127462 b_l127462 := by
  have f0 : InstrSpec 0x127462 [0x89, 0xCE] (fun s => s.RIP = 0x127462) (movR32R32Effect 0x127462 2 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x127462 2 6 1).toInstrSpec (mov_r32_r32_effect_step 0x127462 0xce (by decide)) pre_rip
  have f1 : InstrSpec 0x127464 [0xC1, 0xEE, 0x08] (fun s => s.RIP = 0x127464) (shrR32Effect 0x127464 3 6 8)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x127464 3 6 8).toInstrSpec (shr_r32_imm8_effect_step 0x127464 0xee 0x8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127467 [0x48, 0xBF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x127467) (movR64Imm64Effect 0x127467 7 0xffffffff00000000)
      [] [] [.reg 7, .rip] :=
    (movR64Imm64Effect_footprint 0x127467 7 0xffffffff00000000).toInstrSpec (mov_r64_imm64_effect_step 0x127467 0x48 0xbf (by decide) (by decide) 0xffffffff00000000) pre_rip
  have f3 : InstrSpec 0x127471 [0x4C, 0x21, 0xFF] (fun s => s.RIP = 0x127471) (andR64R64Effect 0x127471 7 15)
      [.gpr 7, .gpr 15] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x127471 7 15).toInstrSpec (and_r64_r64_effect_step 0x127471 0x4c 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127464) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127467) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127471) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 59), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127474) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 61) (jmp_rel8_effect_step 0x127474 0x2c (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l127462 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127462 :=
  Rest.liftedBlock (rest_l127462 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127462 x hx)

theorem rest_l127476 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127476 bytes_l127476) (entryMap (live .l127476))
      5 0x127476 bytes_l127476 b_l127476 := by
  have f0 : InstrSpec 0x127476 [0x48, 0xFF, 0xC0] (fun s => s.RIP = 0x127476) (incR64Effect 0x127476 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (incR64Effect_footprint 0x127476 0).toInstrSpec (inc_r64_effect_step 0x127476 0x48 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127479 [0x49, 0x89, 0x46, 0x10] (StorePre 0x127479 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x127479 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127479 0 (.base 14 (.d8 0x10)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x127479 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x127479 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12747d [0x45, 0x8B, 0x7E, 0x18] (LoadPre 0x12747d (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x12747d + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x12747d 15 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x12747d 15 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x12747d 0x45 (by decide) 7 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x127481 [0x44, 0x39, 0xFD] (fun s => s.RIP = 0x127481) (cmpR32R32Effect 0x127481 3 5 15)
      [.gpr 5, .gpr 15] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x127481 3 5 15).toInstrSpec (cmp_r32_r32_rex_effect_step 0x127481 0x44 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127479) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12747d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127481) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127484) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x127484 6 0x70) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127476 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127476 :=
  Rest.liftedBlock (rest_l127476 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127476 x hx)

theorem rest_l127486 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127486 bytes_l127486) (entryMap (live .l127486))
      3 0x127486 bytes_l127486 b_l127486 := by
  have f0 : InstrSpec 0x127486 [0x41, 0x8D, 0x47, 0x01] (fun s => s.RIP = 0x127486) (leaR32Effect 0x127486 4 0 (.base 15 (.d8 0x1)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (leaR32Effect_footprint 0x127486 4 0 (.base 15 (.d8 0x1))).toInstrSpec (lea_r32_rex_effect_step 0x127486 0x41 (by decide) 0 (.base 15 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12748a [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x12748a) (shlR64Effect 0x12748a 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x12748a 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x12748a 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12748e [0x48, 0x83, 0xC8, 0x03] (fun s => s.RIP = 0x12748e) (orR64Imm8Effect 0x12748e 0 0x3)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x12748e 0 0x3).toInstrSpec (or_r64_imm8_effect_step 0x12748e 0x48 0xc8 0x3 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (7, 7), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12748a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (7, 7), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12748e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (7, 7), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127492) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l127486 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127486 :=
  Rest.liftedBlock (rest_l127486 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127486 x hx)

theorem rest_l127492 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127492 bytes_l127492) (entryMap (live .l127492))
      5 0x127492 bytes_l127492 b_l127492 := by
  have f0 : InstrSpec 0x127492 [0x44, 0x89, 0xFE] (fun s => s.RIP = 0x127492) (movR32R32Effect 0x127492 3 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x127492 3 6 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x127492 0x44 0xfe (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127495 [0xC1, 0xEE, 0x08] (fun s => s.RIP = 0x127495) (shrR32Effect 0x127495 3 6 8)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x127495 3 6 8).toInstrSpec (shr_r32_imm8_effect_step 0x127495 0xee 0x8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127498 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127498) (movR32Imm32Effect 0x127498 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x127498 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x127498 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x12749d [0x31, 0xFF] (fun s => s.RIP = 0x12749d) (xorR32R32Effect 0x12749d 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12749d 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x12749d 0xff (by decide)) pre_rip
  have f4 : InstrSpec 0x12749f [0x44, 0x89, 0xF9] (fun s => s.RIP = 0x12749f) (movR32R32Effect 0x12749f 3 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x12749f 3 1 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x12749f 0x44 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (6, 53), (7, 7), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127495) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (6, 55), (7, 7), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127498) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 57), (3, 3), (4, 4), (6, 55), (7, 7), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12749d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 57), (3, 3), (4, 4), (6, 55), (7, 59), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12749f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 57), (3, 3), (4, 4), (6, 55), (7, 59), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274a2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 63) (by decide) rfl

theorem block_l127492 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127492 :=
  Rest.liftedBlock (rest_l127492 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127492 x hx)

theorem rest_l1274a2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1274a2 bytes_l1274a2) (entryMap (live .l1274a2))
      18 0x1274a2 bytes_l1274a2 b_l1274a2 := by
  have f0 : InstrSpec 0x1274a2 [0x45, 0x89, 0xF8] (fun s => s.RIP = 0x1274a2) (movR32R32Effect 0x1274a2 3 8 15)
      [.gpr 15] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x1274a2 3 8 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x1274a2 0x45 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1274a5 [0x49, 0x09, 0xF8] (fun s => s.RIP = 0x1274a5) (orR64R64Effect 0x1274a5 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1274a5 8 7).toInstrSpec (or_r64_r64_effect_step 0x1274a5 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1274a8 [0x48, 0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x1274a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1274a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1274a8 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1274a8 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1274a8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1274ad [0x48, 0x89, 0x7B, 0x30] (StorePre 0x1274ad 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x1274ad + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1274ad 7 (.base 3 (.d8 0x30)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1274ad 7 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1274ad 0x48 (by decide) 7 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1274b1 [0x48, 0x8B, 0x7C, 0x24, 0x10] (LoadPre 0x1274b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1274b1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1274b1 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1274b1 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1274b1 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1274b6 [0x48, 0x89, 0x7B, 0x28] (StorePre 0x1274b6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1274b6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1274b6 7 (.base 3 (.d8 0x28)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1274b6 7 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1274b6 0x48 (by decide) 7 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1274ba [0x48, 0x8B, 0x3C, 0x24] (LoadPre 0x1274ba (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1274ba + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1274ba 7 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1274ba 7 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1274ba 0x48 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1274be [0x4C, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x1274be (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1274be + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1274be 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1274be 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1274be 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1274c3 [0x4C, 0x89, 0x4B, 0x20] (StorePre 0x1274c3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1274c3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1274c3 9 (.base 3 (.d8 0x20)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1274c3 9 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1274c3 0x4c (by decide) 1 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1274c7 [0x48, 0x89, 0x7B, 0x18] (StorePre 0x1274c7 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1274c7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1274c7 7 (.base 3 (.d8 0x18)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1274c7 7 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1274c7 0x48 (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1274cb [0x89, 0x13] (StorePre 0x1274cb 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1274cb + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1274cb 2 (.base 3 .none))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1274cb 2 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x1274cb 2 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1274cd [0x88, 0x4B, 0x04] (StorePre 0x1274cd 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1274cd + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1274cd 3 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x1274cd 3 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m8_r8_effect_step 0x1274cd 1 (by decide) (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1274d0 [0x89, 0xF1] (fun s => s.RIP = 0x1274d0) (movR32R32Effect 0x1274d0 2 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1274d0 2 1 6).toInstrSpec (mov_r32_r32_effect_step 0x1274d0 0xf1 (by decide)) pre_rip
  have f13 : InstrSpec 0x1274d2 [0xC1, 0xE9, 0x10] (fun s => s.RIP = 0x1274d2) (shrR32Effect 0x1274d2 3 1 16)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1274d2 3 1 16).toInstrSpec (shr_r32_imm8_effect_step 0x1274d2 0xe9 0x10 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1274d5 [0x88, 0x4B, 0x07] (StorePre 0x1274d5 3 (fun s => AddrMode.addr (.base 3 (.d8 0x7)) s (0x1274d5 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1274d5 3 1 (.base 3 (.d8 0x7)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x1274d5 3 1 (.base 3 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x1274d5 1 (by decide) (.base 3 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1274d8 [0x66, 0x89, 0x73, 0x05] (StorePre 0x1274d8 4 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x1274d8 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x1274d8 4 6 (.base 3 (.d8 0x5)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x1274d8 4 6 (.base 3 (.d8 0x5))).toInstrSpec (mov_m16_r16_effect_step 0x1274d8 6 (.base 3 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x1274dc [0x48, 0x89, 0x43, 0x08] (StorePre 0x1274dc 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1274dc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1274dc 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1274dc 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1274dc 0x48 (by decide) 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x1274e0 [0x4C, 0x89, 0x43, 0x10] (StorePre 0x1274e0 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1274e0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1274e0 8 (.base 3 (.d8 0x10)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1274e0 8 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1274e0 0x4c (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274a5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274a8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 57), (8, 55), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274ad) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 57), (8, 55), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274b1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 60), (8, 55), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274b6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 60), (8, 55), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274ba) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 63), (8, 55), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274be) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 63), (8, 55), (9, 65), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274c3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 63), (8, 55), (9, 65), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274c7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 63), (8, 55), (9, 65), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274cb) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 63), (8, 55), (9, 65), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274cd) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 63), (8, 55), (9, 65), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274d0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 71), (2, 2), (3, 3), (4, 4), (6, 6), (7, 63), (8, 55), (9, 65), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274d2) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (6, 6), (7, 63), (8, 55), (9, 65), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274d5) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (6, 6), (7, 63), (8, 55), (9, 65), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274d8) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (6, 6), (7, 63), (8, 55), (9, 65), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274dc) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (6, 6), (7, 63), (8, 55), (9, 65), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274e0) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (6, 6), (7, 63), (8, 55), (9, 65), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274e4) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 79) (by decide) rfl

theorem block_l1274a2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1274a2 :=
  Rest.liftedBlock (rest_l1274a2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1274a2 x hx)

theorem rest_l1274e4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1274e4 bytes_l1274e4) (entryMap (live .l1274e4))
      9 0x1274e4 bytes_l1274e4 b_l1274e4 := by
  have f0 : InstrSpec 0x1274e4 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1274e4) (movR64R64Effect 0x1274e4 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1274e4 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1274e4 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1274e7 [0x48, 0x83, 0xC4, 0x78] (fun s => s.RIP = 0x1274e7) (addR64Imm8Effect 0x1274e7 4 0x78)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1274e7 4 0x78).toInstrSpec (add_r64_imm8_effect_step 0x1274e7 0x48 0xc4 0x78 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1274eb [0x5B] (PopPre 0x1274eb) (popR64Effect 0x1274eb 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1274eb 1 3).toInstrSpec (pop_r64_effect_step 0x1274eb 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1274ec [0x41, 0x5C] (PopPre 0x1274ec) (popR64Effect 0x1274ec 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1274ec 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1274ec 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1274ee [0x41, 0x5D] (PopPre 0x1274ee) (popR64Effect 0x1274ee 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1274ee 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1274ee 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1274f0 [0x41, 0x5E] (PopPre 0x1274f0) (popR64Effect 0x1274f0 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1274f0 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1274f0 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1274f2 [0x41, 0x5F] (PopPre 0x1274f2) (popR64Effect 0x1274f2 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1274f2 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1274f2 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1274f4 [0x5D] (PopPre 0x1274f4) (popR64Effect 0x1274f4 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1274f4 1 5).toInstrSpec (pop_r64_effect_step 0x1274f4 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x1274f5 [0xC3] (RetPre 0x1274f5) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1274f5).toInstrSpec (ret_effect_step 0x1274f5) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274e7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274eb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274ec) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274ee) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274f0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274f2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274f4) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274f5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l1274e4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1274e4 :=
  Rest.liftedBlock (rest_l1274e4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1274e4 x hx)

theorem rest_l1274f6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1274f6 bytes_l1274f6) (entryMap (live .l1274f6))
      10 0x1274f6 bytes_l1274f6 b_l1274f6 := by
  have f0 : InstrSpec 0x1274f6 [0x41, 0x89, 0x6E, 0x18] (StorePre 0x1274f6 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1274f6 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1274f6 5 (.base 14 (.d8 0x18)))
      [.gpr 5, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x1274f6 5 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x1274f6 0x41 (by decide) 5 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1274fa [0x48, 0x8D, 0x54, 0x24, 0x68] (fun s => s.RIP = 0x1274fa) (leaR64Effect 0x1274fa 2 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1274fa 2 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (lea_r64_effect_step 0x1274fa 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1274ff [0x49, 0x8B, 0x45, 0x00] (LoadPre 0x1274ff (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x1274ff + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1274ff 0 (.base 13 (.d8 0x0)))
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1274ff 0 (.base 13 (.d8 0x0))).toInstrSpec (mov_r64_m64_effect_step 0x1274ff 0x49 (by decide) 0 (.base 13 (.d8 0x0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x127503 [0x49, 0x8B, 0x4D, 0x08] (LoadPre 0x127503 (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x127503 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x127503 1 (.base 13 (.d8 0x8)))
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x127503 1 (.base 13 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x127503 0x49 (by decide) 1 (.base 13 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x127507 [0x48, 0x89, 0x4C, 0x24, 0x70] (StorePre 0x127507 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x127507 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127507 1 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x127507 1 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x127507 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12750c [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x12750c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x12750c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12750c 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12750c 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x12750c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x127511 [0x4C, 0x89, 0x74, 0x24, 0x60] (StorePre 0x127511 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x127511 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127511 14 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x127511 14 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x127511 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x127516 [0x48, 0x8D, 0x7C, 0x24, 0x20] (fun s => s.RIP = 0x127516) (leaR64Effect 0x127516 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x127516 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x127516 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12751b [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x12751b) (movR64R64Effect 0x12751b 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12751b 6 14).toInstrSpec (mov_r64_r64_effect_step 0x12751b 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x12751e [0xE8, 0xBD, 0xD6, 0xFF, 0xFF] (PushPre 0x12751e 5) (callEffect (fun _ => 0x124be0) 0x127523)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12751e 0x124be0 0x127523).toInstrSpec (call_rel32_effect_step 0x12751e 0xffffd6bd (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274fa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1274ff) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127503) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127507) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12750c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127511) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127516) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12751b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12751e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 67), (5, 5), (6, 65), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124be0) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l1274f6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1274f6 :=
  Rest.liftedBlock (rest_l1274f6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1274f6 x hx)

theorem rest_l127523 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127523 bytes_l127523) (entryMap (live .l127523))
      17 0x127523 bytes_l127523 b_l127523 := by
  have f0 : InstrSpec 0x127523 [0x45, 0x8B, 0x46, 0x18] (LoadPre 0x127523 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x127523 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x127523 8 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x127523 8 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x127523 0x45 (by decide) 0 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127527 [0x41, 0x8B, 0x4E, 0x1C] (LoadPre 0x127527 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x127527 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x127527 1 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x127527 1 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x127527 0x41 (by decide) 1 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12752b [0x41, 0x39, 0xC8] (fun s => s.RIP = 0x12752b) (cmpR32R32Effect 0x12752b 3 8 1)
      [.gpr 8, .gpr 1] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x12752b 3 8 1).toInstrSpec (cmp_r32_r32_rex_effect_step 0x12752b 0x41 0xc8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12752e [0x0F, 0x96, 0xC0] (fun s => s.RIP = 0x12752e) (atFlags (condHolds 6) (setccR8Effect 0x12752e 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x12752e 3 0 6).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x12752e 6 0xc0 (by decide) (by decide) c)) pre_rip
  have f4 : InstrSpec 0x127531 [0x48, 0x8B, 0x54, 0x24, 0x58] (LoadPre 0x127531 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x127531 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127531 2 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x127531 2 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x127531 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x127536 [0x49, 0x89, 0x16] (StorePre 0x127536 3 (fun s => AddrMode.addr (.base 14 .none) s (0x127536 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x127536 2 (.base 14 .none))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x127536 2 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x127536 0x49 (by decide) 2 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x127539 [0x4D, 0x89, 0x66, 0x08] (StorePre 0x127539 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x127539 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127539 12 (.base 14 (.d8 0x8)))
      [.gpr 12, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x127539 12 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x127539 0x4d (by decide) 4 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x12753d [0x45, 0x89, 0x7E, 0x18] (StorePre 0x12753d 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x12753d + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x12753d 15 (.base 14 (.d8 0x18)))
      [.gpr 15, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x12753d 15 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x12753d 0x45 (by decide) 7 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x127541 [0x49, 0x8B, 0x56, 0x10] (LoadPre 0x127541 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x127541 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x127541 2 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x127541 2 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x127541 0x49 (by decide) 2 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x127545 [0x48, 0x83, 0xFA, 0x01] (fun s => s.RIP = 0x127545) (cmpR64Imm8Effect 0x127545 2 0x1)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x127545 2 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x127545 0x48 0xfa 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x127549 [0x48, 0x83, 0xD2, 0xFF] (fun s => s.RIP = 0x127549) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x127549 2 0xff))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x127549 2 0xff).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x127549 0x48 0xd2 0xff c (by decide) (by decide) (by decide))) pre_rip
  have f11 : InstrSpec 0x12754d [0x49, 0x89, 0x56, 0x10] (StorePre 0x12754d 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x12754d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12754d 2 (.base 14 (.d8 0x10)))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x12754d 2 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x12754d 0x49 (by decide) 2 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x127551 [0x8B, 0x54, 0x24, 0x20] (LoadPre 0x127551 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x127551 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x127551 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x127551 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r32_m32_low_effect_step 0x127551 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x127555 [0x83, 0xFA, 0x02] (fun s => s.RIP = 0x127555) (cmpR32Imm8Effect 0x127555 3 2 0x2)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x127555 3 2 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x127555 0xfa 0x2 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x127558 [0x40, 0x0F, 0x95, 0xC6] (fun s => s.RIP = 0x127558) (atFlags (condHolds 5) (setccR8Effect 0x127558 4 6))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 6, .rip] :=
    (setccR8Effect_footprint 0x127558 4 6 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x127558 5 0x40 (by decide) 0xc6 (by decide) c)) pre_rip
  have f15 : InstrSpec 0x12755c [0x40, 0x08, 0xC6] (fun s => s.RIP = 0x12755c) (orR8R8Effect 0x12755c 3 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (orR8R8Effect_footprint 0x12755c 3 6 0).toInstrSpec (or_r8_r8_rex_effect_step 0x12755c 0x40 0xc6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127527) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12752b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12752e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127531) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 55), (2, 62), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127536) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 60), (1, 55), (2, 62), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127539) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 60), (1, 55), (2, 62), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12753d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 60), (1, 55), (2, 62), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127541) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 60), (1, 55), (2, 67), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127545) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 60), (1, 55), (2, 67), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127549) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 60), (1, 55), (2, 71), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12754d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 60), (1, 55), (2, 71), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127551) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 60), (1, 55), (2, 74), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127555) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 60), (1, 55), (2, 74), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127558) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 60), (1, 55), (2, 74), (3, 3), (4, 4), (6, 78), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12755c) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 60), (1, 55), (2, 74), (3, 3), (4, 4), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12755f) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 82) (jcc_rel8_effect_step 0x12755f 4 0x4c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127523 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127523 :=
  Rest.liftedBlock (rest_l127523 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127523 x hx)

theorem rest_l127561 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127561 bytes_l127561) (entryMap (live .l127561))
      13 0x127561 bytes_l127561 b_l127561 := by
  have f0 : InstrSpec 0x127561 [0x8B, 0x4C, 0x24, 0x24] (LoadPre 0x127561 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x127561 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x127561 1 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x127561 1 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r32_m32_low_effect_step 0x127561 1 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127565 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x127565 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x127565 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127565 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x127565 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x127565 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12756a [0x4C, 0x8B, 0x7C, 0x24, 0x30] (LoadPre 0x12756a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x12756a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12756a 15 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x12756a 15 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x12756a 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12756f [0x48, 0x8B, 0x74, 0x24, 0x38] (LoadPre 0x12756f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x12756f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12756f 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12756f 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x12756f 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x127574 [0x48, 0x89, 0x34, 0x24] (StorePre 0x127574 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x127574 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127574 6 (.sib 4 none 0 .none))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x127574 6 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x127574 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x127578 [0x48, 0x8B, 0x74, 0x24, 0x40] (LoadPre 0x127578 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x127578 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127578 6 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x127578 6 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x127578 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x12757d [0x48, 0x89, 0x74, 0x24, 0x08] (StorePre 0x12757d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12757d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12757d 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12757d 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x12757d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x127582 [0x48, 0x8B, 0x74, 0x24, 0x48] (LoadPre 0x127582 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x127582 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127582 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x127582 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x127582 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x127587 [0x48, 0x89, 0x74, 0x24, 0x10] (StorePre 0x127587 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x127587 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127587 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x127587 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x127587 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12758c [0x48, 0x8B, 0x74, 0x24, 0x50] (LoadPre 0x12758c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x12758c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12758c 6 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12758c 6 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x12758c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x127591 [0x48, 0x89, 0x74, 0x24, 0x18] (StorePre 0x127591 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x127591 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127591 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x127591 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x127591 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x127596 [0x83, 0xFA, 0x02] (fun s => s.RIP = 0x127596) (cmpR32Imm8Effect 0x127596 3 2 0x2)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x127596 3 2 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x127596 0xfa 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127565) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12756a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12756f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127574) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127578) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12757d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127582) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 65), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127587) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 65), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12758c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127591) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127596) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 57), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127599) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 73) (jcc_rel32_effect_step 0x127599 5 0xfffffec3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127561 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127561 :=
  Rest.liftedBlock (rest_l127561 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127561 x hx)

theorem rest_l12759f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12759f bytes_l12759f) (entryMap (live .l12759f))
      3 0x12759f bytes_l12759f b_l12759f := by
  have f0 : InstrSpec 0x12759f [0x88, 0x4B, 0x04] (StorePre 0x12759f 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x12759f + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x12759f 3 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x12759f 3 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m8_r8_effect_step 0x12759f 1 (by decide) (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1275a2 [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x1275a2 6 (fun s => AddrMode.addr (.base 3 .none) s (0x1275a2 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x1275a2 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1275a2 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x1275a2 (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275a2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275a8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x1275a8 0xffffff37 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12759f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12759f :=
  Rest.liftedBlock (rest_l12759f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12759f x hx)

theorem rest_l1275ad [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1275ad bytes_l1275ad) (entryMap (live .l1275ad))
      11 0x1275ad bytes_l1275ad b_l1275ad := by
  have f0 : InstrSpec 0x1275ad [0x41, 0x29, 0xC8] (fun s => s.RIP = 0x1275ad) (subR32R32Effect 0x1275ad 3 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (subR32R32Effect_footprint 0x1275ad 3 8 1).toInstrSpec (sub_r32_r32_rex_effect_step 0x1275ad 0x41 0xc8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1275b0 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x1275b0 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1275b0 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1275b0 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x1275b0 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x1275b0 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1275b5 [0x89, 0xCE] (fun s => s.RIP = 0x1275b5) (movR32R32Effect 0x1275b5 2 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x1275b5 2 6 1).toInstrSpec (mov_r32_r32_effect_step 0x1275b5 0xce (by decide)) pre_rip
  have f3 : InstrSpec 0x1275b7 [0xC1, 0xEE, 0x08] (fun s => s.RIP = 0x1275b7) (shrR32Effect 0x1275b7 3 6 8)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x1275b7 3 6 8).toInstrSpec (shr_r32_imm8_effect_step 0x1275b7 0xee 0x8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1275ba [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x1275ba) (movR64R64Effect 0x1275ba 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1275ba 0 1).toInstrSpec (mov_r64_r64_effect_step 0x1275ba 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1275bd [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x1275bd) (shlR64Effect 0x1275bd 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x1275bd 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x1275bd 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1275c1 [0x48, 0x83, 0xC8, 0x13] (fun s => s.RIP = 0x1275c1) (orR64Imm8Effect 0x1275c1 0 0x13)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x1275c1 0 0x13).toInstrSpec (or_r64_imm8_effect_step 0x1275c1 0x48 0xc8 0x13 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1275c5 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1275c5) (movR32Imm32Effect 0x1275c5 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1275c5 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1275c5 0xba (by decide) 0x1) pre_rip
  have f8 : InstrSpec 0x1275ca [0x31, 0xFF] (fun s => s.RIP = 0x1275ca) (xorR32R32Effect 0x1275ca 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1275ca 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x1275ca 0xff (by decide)) pre_rip
  have f9 : InstrSpec 0x1275cc [0x45, 0x89, 0xC7] (fun s => s.RIP = 0x1275cc) (movR32R32Effect 0x1275cc 3 15 8)
      [.gpr 8] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x1275cc 3 15 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x1275cc 0x45 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (7, 7), (8, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275b0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (3, 3), (4, 4), (7, 7), (8, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275b5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 56), (7, 7), (8, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275b7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 58), (7, 7), (8, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275ba) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (3, 3), (4, 4), (6, 58), (7, 7), (8, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275bd) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 1), (3, 3), (4, 4), (6, 58), (7, 7), (8, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275c1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 1), (3, 3), (4, 4), (6, 58), (7, 7), (8, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275c5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 1), (2, 66), (3, 3), (4, 4), (6, 58), (7, 7), (8, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275ca) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 64), (1, 1), (2, 66), (3, 3), (4, 4), (6, 58), (7, 68), (8, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275cc) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 64), (1, 1), (2, 66), (3, 3), (4, 4), (6, 58), (7, 68), (8, 53), (10, 10), (11, 11), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275cf) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 72) (jmp_rel32_effect_step 0x1275cf 0xfffffece (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1275ad [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1275ad :=
  Rest.liftedBlock (rest_l1275ad code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1275ad x hx)

theorem rest_l1275d4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1275d4 bytes_l1275d4) (entryMap (live .l1275d4))
      4 0x1275d4 bytes_l1275d4 b_l1275d4 := by
  have f0 : InstrSpec 0x1275d4 [0x31, 0xD2] (fun s => s.RIP = 0x1275d4) (xorR32R32Effect 0x1275d4 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1275d4 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x1275d4 0xd2 (by decide)) pre_rip
  have f1 : InstrSpec 0x1275d6 [0xB8, 0x0C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1275d6) (movR32Imm32Effect 0x1275d6 5 0 0xc)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1275d6 5 0 0xc).toInstrSpec (mov_r32_imm32_effect_step 0x1275d6 0xb8 (by decide) 0xc) pre_rip
  have f2 : InstrSpec 0x1275db [0x31, 0xFF] (fun s => s.RIP = 0x1275db) (xorR32R32Effect 0x1275db 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1275db 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x1275db 0xff (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275d6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275db) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 57), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275dd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x1275dd 0xfffffec0 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1275d4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1275d4 :=
  Rest.liftedBlock (rest_l1275d4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1275d4 x hx)

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

theorem_by block_l1273c0_eval :
    program.runBlock (dialect code) ⟨.l1273c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1273e1_eval :
    program.runBlock (dialect code) ⟨.l1273e1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127402_eval :
    program.runBlock (dialect code) ⟨.l127402, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12740b_eval :
    program.runBlock (dialect code) ⟨.l12740b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127426_eval :
    program.runBlock (dialect code) ⟨.l127426, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12742d_eval :
    program.runBlock (dialect code) ⟨.l12742d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127462_eval :
    program.runBlock (dialect code) ⟨.l127462, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127476_eval :
    program.runBlock (dialect code) ⟨.l127476, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127486_eval :
    program.runBlock (dialect code) ⟨.l127486, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127492_eval :
    program.runBlock (dialect code) ⟨.l127492, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1274a2_eval :
    program.runBlock (dialect code) ⟨.l1274a2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1274e4_eval :
    program.runBlock (dialect code) ⟨.l1274e4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1274f6_eval :
    program.runBlock (dialect code) ⟨.l1274f6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127523_eval :
    program.runBlock (dialect code) ⟨.l127523, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127561_eval :
    program.runBlock (dialect code) ⟨.l127561, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12759f_eval :
    program.runBlock (dialect code) ⟨.l12759f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1275ad_eval :
    program.runBlock (dialect code) ⟨.l1275ad, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1275d4_eval :
    program.runBlock (dialect code) ⟨.l1275d4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Generate.LIR
