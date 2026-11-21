import K256.Proofs.Ecdh.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Ecdh.LIR.Generated.Values

namespace K256.Proofs.Ecdh.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR

theorem rest_l1267c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1267c0 bytes_l1267c0) (entryMap (live .l1267c0))
      12 0x1267c0 bytes_l1267c0 b_l1267c0 := by
  have f0 : InstrSpec 0x1267c0 [0x55] (PushPre 0x1267c0 1) (pushR64Effect 0x1267c0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1267c0 1 5).toInstrSpec (push_r64_effect_step 0x1267c0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1267c1 [0x41, 0x57] (PushPre 0x1267c1 2) (pushR64Effect 0x1267c1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1267c1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1267c1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1267c3 [0x41, 0x56] (PushPre 0x1267c3 2) (pushR64Effect 0x1267c3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1267c3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1267c3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1267c5 [0x41, 0x55] (PushPre 0x1267c5 2) (pushR64Effect 0x1267c5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1267c5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1267c5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1267c7 [0x41, 0x54] (PushPre 0x1267c7 2) (pushR64Effect 0x1267c7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1267c7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1267c7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1267c9 [0x53] (PushPre 0x1267c9 1) (pushR64Effect 0x1267c9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1267c9 1 3).toInstrSpec (push_r64_effect_step 0x1267c9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1267ca [0x48, 0x81, 0xEC, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1267ca) (subR64Imm32Effect 0x1267ca 4 0x98)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x1267ca 4 0x98).toInstrSpec (sub_r64_imm32_effect_step 0x1267ca 0x48 0xec 0x98 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1267d1 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x1267d1) (movR64R64Effect 0x1267d1 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1267d1 3 7).toInstrSpec (mov_r64_r64_effect_step 0x1267d1 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1267d4 [0x44, 0x8B, 0x7E, 0x1C] (LoadPre 0x1267d4 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x1267d4 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1267d4 15 (.base 6 (.d8 0x1c)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x1267d4 15 (.base 6 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x1267d4 0x44 (by decide) 7 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1267d8 [0x8B, 0x6A, 0x08] (LoadPre 0x1267d8 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1267d8 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1267d8 5 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR32M32LowEffect_footprint 0x1267d8 5 (.base 2 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x1267d8 5 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1267db [0x44, 0x01, 0xFD] (fun s => s.RIP = 0x1267db) (addR32R32Effect 0x1267db 3 5 15)
      [.gpr 5, .gpr 15] [] [.reg 5, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1267db 3 5 15).toInstrSpec (add_r32_r32_rex_effect_step 0x1267db 0x44 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267c3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267c5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267c7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267c9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267ca) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267d1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267d4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267d8) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267db) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267de) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 76) (jcc_rel32_effect_step 0x1267de 2 0x238) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1267c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1267c0 :=
  Rest.liftedBlock (rest_l1267c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1267c0 x hx)

theorem rest_l1267e4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1267e4 bytes_l1267e4) (entryMap (live .l1267e4))
      9 0x1267e4 bytes_l1267e4 b_l1267e4 := by
  have f0 : InstrSpec 0x1267e4 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x1267e4) (movR64R64Effect 0x1267e4 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1267e4 13 2).toInstrSpec (mov_r64_r64_effect_step 0x1267e4 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1267e7 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x1267e7) (movR64R64Effect 0x1267e7 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1267e7 14 6).toInstrSpec (mov_r64_r64_effect_step 0x1267e7 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1267ea [0x48, 0x8B, 0x36] (LoadPre 0x1267ea (fun s => AddrMode.addr (.base 6 .none) s (0x1267ea + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1267ea 6 (.base 6 .none))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1267ea 6 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1267ea 0x48 (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1267ed [0x4D, 0x8B, 0x66, 0x08] (LoadPre 0x1267ed (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1267ed + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1267ed 12 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x1267ed 12 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1267ed 0x4d (by decide) 4 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1267f1 [0x48, 0x8D, 0x7C, 0x24, 0x40] (fun s => s.RIP = 0x1267f1) (leaR64Effect 0x1267f1 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1267f1 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (lea_r64_effect_step 0x1267f1 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1267f6 [0x48, 0x89, 0x74, 0x24, 0x78] (StorePre 0x1267f6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1267f6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1267f6 6 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1267f6 6 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x1267f6 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1267fb [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x1267fb) (movR64R64Effect 0x1267fb 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1267fb 2 12).toInstrSpec (mov_r64_r64_effect_step 0x1267fb 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1267fe [0x89, 0xE9] (fun s => s.RIP = 0x1267fe) (movR32R32Effect 0x1267fe 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1267fe 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x1267fe 0xe9 (by decide)) pre_rip
  have f8 : InstrSpec 0x126800 [0xE8, 0x4B, 0x14, 0x00, 0x00] (PushPre 0x126800 5) (callEffect (fun _ => 0x127c50) 0x126805)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x126800 0x127c50 0x126805).toInstrSpec (call_rel32_effect_step 0x126800 0x144b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267e7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267ea) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267ed) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267f1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267f6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267fb) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 64), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267fe) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126800) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 68), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c50) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 70) (by decide) (by decide) rfl rfl

theorem block_l1267e4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1267e4 :=
  Rest.liftedBlock (rest_l1267e4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1267e4 x hx)

theorem rest_l126805 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126805 bytes_l126805) (entryMap (live .l126805))
      3 0x126805 bytes_l126805 b_l126805 := by
  have f0 : InstrSpec 0x126805 [0x8B, 0x54, 0x24, 0x40] (LoadPre 0x126805 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x126805 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126805 2 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x126805 2 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r32_m32_low_effect_step 0x126805 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126809 [0x83, 0xFA, 0x02] (fun s => s.RIP = 0x126809) (cmpR32Imm8Effect 0x126809 3 2 0x2)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x126809 3 2 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x126809 0xfa 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126809) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12680c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x12680c 5 0x22) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126805 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126805 :=
  Rest.liftedBlock (rest_l126805 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126805 x hx)

theorem rest_l12680e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12680e bytes_l12680e) (entryMap (live .l12680e))
      7 0x12680e bytes_l12680e b_l12680e := by
  have f0 : InstrSpec 0x12680e [0x48, 0x8B, 0x44, 0x24, 0x48] (LoadPre 0x12680e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x12680e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12680e 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12680e 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x12680e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126813 [0x48, 0x8B, 0x4C, 0x24, 0x50] (LoadPre 0x126813 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126813 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126813 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x126813 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x126813 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126818 [0x49, 0x89, 0x06] (StorePre 0x126818 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126818 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126818 0 (.base 14 .none))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126818 0 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x126818 0x49 (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x12681b [0x49, 0x89, 0x4E, 0x08] (StorePre 0x12681b 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x12681b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12681b 1 (.base 14 (.d8 0x8)))
      [.gpr 1, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x12681b 1 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x12681b 0x49 (by decide) 1 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12681f [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x12681f (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x12681f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12681f 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12681f 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x12681f 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x126823 [0x48, 0x83, 0xF8, 0x3F] (fun s => s.RIP = 0x126823) (cmpR64Imm8Effect 0x126823 0 0x3f)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x126823 0 0x3f).toInstrSpec (cmp_r64_imm8_effect_step 0x126823 0x48 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126813) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126818) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12681b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12681f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126823) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126827) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x126827 6 0x4c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12680e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12680e :=
  Rest.liftedBlock (rest_l12680e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12680e x hx)

theorem rest_l126829 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126829 bytes_l126829) (entryMap (live .l126829))
      2 0x126829 bytes_l126829 b_l126829 := by
  have f0 : InstrSpec 0x126829 [0xB8, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126829) (movR32Imm32Effect 0x126829 5 0 0x6)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x126829 5 0 0x6).toInstrSpec (mov_r32_imm32_effect_step 0x126829 0xb8 (by decide) 0x6) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12682e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x12682e 0x65 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126829 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126829 :=
  Rest.liftedBlock (rest_l126829 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126829 x hx)

theorem rest_l126830 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126830 bytes_l126830) (entryMap (live .l126830))
      11 0x126830 bytes_l126830 b_l126830 := by
  have f0 : InstrSpec 0x126830 [0x8B, 0x4C, 0x24, 0x44] (LoadPre 0x126830 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x126830 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126830 1 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x126830 1 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_r32_m32_low_effect_step 0x126830 1 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126834 [0x48, 0x8B, 0x44, 0x24, 0x48] (LoadPre 0x126834 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126834 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126834 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126834 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x126834 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126839 [0x48, 0x8B, 0x74, 0x24, 0x50] (LoadPre 0x126839 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126839 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126839 6 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x126839 6 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x126839 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12683e [0x48, 0x8B, 0x7C, 0x24, 0x58] (LoadPre 0x12683e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12683e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12683e 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12683e 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x12683e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x126843 [0x48, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x126843 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126843 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126843 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126843 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x126843 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x126848 [0x48, 0x8B, 0x7C, 0x24, 0x60] (LoadPre 0x126848 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126848 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126848 7 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126848 7 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x126848 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x12684d [0x48, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x12684d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12684d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12684d 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12684d 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x12684d 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x126852 [0x48, 0x8B, 0x7C, 0x24, 0x68] (LoadPre 0x126852 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x126852 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126852 7 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126852 7 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x126852 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x126857 [0x48, 0x89, 0x7C, 0x24, 0x18] (StorePre 0x126857 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126857 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126857 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126857 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x126857 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12685c [0x48, 0x8B, 0x7C, 0x24, 0x70] (LoadPre 0x12685c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x12685c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12685c 7 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12685c 7 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x12685c 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x126861 [0x48, 0x89, 0x7C, 0x24, 0x20] (StorePre 0x126861 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126861 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126861 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126861 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x126861 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126834) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126839) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12683e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126843) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126848) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12684d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126852) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126857) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12685c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126861) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126866) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 71) (by decide) rfl

theorem block_l126830 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126830 :=
  Rest.liftedBlock (rest_l126830 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126830 x hx)

theorem rest_l126866 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126866 bytes_l126866) (entryMap (live .l126866))
      3 0x126866 bytes_l126866 b_l126866 := by
  have f0 : InstrSpec 0x126866 [0x48, 0xBF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x126866) (movR64Imm64Effect 0x126866 7 0xffffffff00000000)
      [] [] [.reg 7, .rip] :=
    (movR64Imm64Effect_footprint 0x126866 7 0xffffffff00000000).toInstrSpec (mov_r64_imm64_effect_step 0x126866 0x48 0xbf (by decide) (by decide) 0xffffffff00000000) pre_rip
  have f1 : InstrSpec 0x126870 [0x48, 0x21, 0xF7] (fun s => s.RIP = 0x126870) (andR64R64Effect 0x126870 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x126870 7 6).toInstrSpec (and_r64_r64_effect_step 0x126870 0x48 0xf7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126870) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126873) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x126873 0x2d (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126866 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126866 :=
  Rest.liftedBlock (rest_l126866 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126866 x hx)

theorem rest_l126875 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126875 bytes_l126875) (entryMap (live .l126875))
      5 0x126875 bytes_l126875 b_l126875 := by
  have f0 : InstrSpec 0x126875 [0x48, 0xFF, 0xC0] (fun s => s.RIP = 0x126875) (incR64Effect 0x126875 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (incR64Effect_footprint 0x126875 0).toInstrSpec (inc_r64_effect_step 0x126875 0x48 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126878 [0x49, 0x89, 0x46, 0x10] (StorePre 0x126878 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126878 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126878 0 (.base 14 (.d8 0x10)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126878 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x126878 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12687c [0x45, 0x8B, 0x7E, 0x18] (LoadPre 0x12687c (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x12687c + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x12687c 15 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x12687c 15 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x12687c 0x45 (by decide) 7 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126880 [0x44, 0x39, 0xFD] (fun s => s.RIP = 0x126880) (cmpR32R32Effect 0x126880 3 5 15)
      [.gpr 5, .gpr 15] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x126880 3 5 15).toInstrSpec (cmp_r32_r32_rex_effect_step 0x126880 0x44 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126878) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12687c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126880) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126883) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel32_effect_step 0x126883 6 0x85) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126875 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126875 :=
  Rest.liftedBlock (rest_l126875 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126875 x hx)

theorem rest_l126889 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126889 bytes_l126889) (entryMap (live .l126889))
      3 0x126889 bytes_l126889 b_l126889 := by
  have f0 : InstrSpec 0x126889 [0x41, 0x8D, 0x47, 0x01] (fun s => s.RIP = 0x126889) (leaR32Effect 0x126889 4 0 (.base 15 (.d8 0x1)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (leaR32Effect_footprint 0x126889 4 0 (.base 15 (.d8 0x1))).toInstrSpec (lea_r32_rex_effect_step 0x126889 0x41 (by decide) 0 (.base 15 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12688d [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x12688d) (shlR64Effect 0x12688d 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x12688d 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x12688d 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126891 [0x48, 0x83, 0xC8, 0x03] (fun s => s.RIP = 0x126891) (orR64Imm8Effect 0x126891 0 0x3)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x126891 0 0x3).toInstrSpec (or_r64_imm8_effect_step 0x126891 0x48 0xc8 0x3 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12688d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126891) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126895) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l126889 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126889 :=
  Rest.liftedBlock (rest_l126889 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126889 x hx)

theorem rest_l126895 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126895 bytes_l126895) (entryMap (live .l126895))
      4 0x126895 bytes_l126895 b_l126895 := by
  have f0 : InstrSpec 0x126895 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126895) (movR32Imm32Effect 0x126895 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x126895 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x126895 0xba (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x12689a [0x31, 0xFF] (fun s => s.RIP = 0x12689a) (xorR32R32Effect 0x12689a 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12689a 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x12689a 0xff (by decide)) pre_rip
  have f2 : InstrSpec 0x12689c [0x44, 0x89, 0xF9] (fun s => s.RIP = 0x12689c) (movR32R32Effect 0x12689c 3 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x12689c 3 1 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x12689c 0x44 0xf9 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12689f [0x44, 0x89, 0xFE] (fun s => s.RIP = 0x12689f) (movR32R32Effect 0x12689f 3 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x12689f 3 6 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x12689f 0x44 0xfe (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12689a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (7, 55), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12689c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 53), (3, 3), (4, 4), (7, 55), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12689f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 57), (2, 53), (3, 3), (4, 4), (6, 59), (7, 55), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268a2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l126895 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126895 :=
  Rest.liftedBlock (rest_l126895 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126895 x hx)

theorem rest_l1268a2_1 [Bindings] (code : CodeMap) :
    Rest (n := 83) code lifted (codeRange 0x1268a2 bytes_l1268a2) [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 75), (8, 77), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x1268f1 bytes_l1268a2_1 b_l1268a2_1 := by
  have f20 : InstrSpec 0x1268f1 [0x48, 0x89, 0x43, 0x08] (StorePre 0x1268f1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1268f1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1268f1 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1268f1 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1268f1 0x48 (by decide) 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x1268f5 [0x48, 0x89, 0x73, 0x10] (StorePre 0x1268f5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1268f5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1268f5 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1268f5 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1268f5 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 75), (8, 77), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268f5) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 75), (8, 77), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268f9) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 85) (by decide) rfl

theorem rest_l1268a2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1268a2 bytes_l1268a2) (entryMap (live .l1268a2))
      22 0x1268a2 bytes_l1268a2 b_l1268a2 := by
  have f0 : InstrSpec 0x1268a2 [0x89, 0xF6] (fun s => s.RIP = 0x1268a2) (movR32R32Effect 0x1268a2 2 6 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x1268a2 2 6 6).toInstrSpec (mov_r32_r32_effect_step 0x1268a2 0xf6 (by decide)) pre_rip
  have f1 : InstrSpec 0x1268a4 [0x48, 0x09, 0xFE] (fun s => s.RIP = 0x1268a4) (orR64R64Effect 0x1268a4 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1268a4 6 7).toInstrSpec (or_r64_r64_effect_step 0x1268a4 0x48 0xfe (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1268a7 [0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x1268a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1268a7 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1268a7 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x1268a7 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r32_m32_low_effect_step 0x1268a7 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1268ab [0x89, 0x7C, 0x24, 0x38] (StorePre 0x1268ab 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1268ab + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1268ab 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1268ab 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m32_r32_low_effect_step 0x1268ab 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1268af [0x48, 0x8B, 0x7C, 0x24, 0x08] (LoadPre 0x1268af (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1268af + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1268af 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1268af 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1268af 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1268b4 [0x4C, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1268b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1268b4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1268b4 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1268b4 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1268b4 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1268b9 [0x4C, 0x89, 0x44, 0x24, 0x30] (StorePre 0x1268b9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1268b9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1268b9 8 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1268b9 8 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1268b9 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1268be [0x48, 0x89, 0x7C, 0x24, 0x28] (StorePre 0x1268be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1268be + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1268be 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1268be 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1268be 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1268c3 [0x8B, 0x7C, 0x24, 0x24] (LoadPre 0x1268c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1268c3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1268c3 7 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x1268c3 7 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r32_m32_low_effect_step 0x1268c3 7 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1268c7 [0x89, 0x7B, 0x34] (StorePre 0x1268c7 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x1268c7 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1268c7 7 (.base 3 (.d8 0x34)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1268c7 7 (.base 3 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x1268c7 7 (.base 3 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1268ca [0x48, 0x8B, 0x7C, 0x24, 0x1C] (LoadPre 0x1268ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1268ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1268ca 7 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1268ca 7 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x1268ca 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1268cf [0x48, 0x89, 0x7B, 0x2C] (StorePre 0x1268cf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x1268cf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1268cf 7 (.base 3 (.d8 0x2c)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1268cf 7 (.base 3 (.d8 0x2c))).toInstrSpec (mov_m64_r64_effect_step 0x1268cf 0x48 (by decide) 7 (.base 3 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1268d3 [0x8B, 0x7C, 0x24, 0x38] (LoadPre 0x1268d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1268d3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1268d3 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x1268d3 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r32_m32_low_effect_step 0x1268d3 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1268d7 [0x89, 0x7B, 0x28] (StorePre 0x1268d7 3 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1268d7 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1268d7 7 (.base 3 (.d8 0x28)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1268d7 7 (.base 3 (.d8 0x28))).toInstrSpec (mov_m32_r32_low_effect_step 0x1268d7 7 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1268da [0x48, 0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x1268da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1268da + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1268da 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1268da 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1268da 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1268df [0x4C, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x1268df (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1268df + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1268df 8 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1268df 8 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1268df 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x1268e4 [0x4C, 0x89, 0x43, 0x20] (StorePre 0x1268e4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1268e4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1268e4 8 (.base 3 (.d8 0x20)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1268e4 8 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1268e4 0x4c (by decide) 0 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x1268e8 [0x48, 0x89, 0x7B, 0x18] (StorePre 0x1268e8 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1268e8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1268e8 7 (.base 3 (.d8 0x18)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1268e8 7 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1268e8 0x48 (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1268ec [0x89, 0x13] (StorePre 0x1268ec 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1268ec + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1268ec 2 (.base 3 .none))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1268ec 2 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x1268ec 2 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1268ee [0x89, 0x4B, 0x04] (StorePre 0x1268ee 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1268ee + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1268ee 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1268ee 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x1268ee 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268a4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268a7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268ab) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268af) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 60), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268b4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 60), (8, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268b9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 60), (8, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268be) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 60), (8, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268c3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 66), (8, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268c7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 66), (8, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268ca) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 69), (8, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268cf) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 69), (8, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268d3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 72), (8, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268d7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 72), (8, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268da) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 75), (8, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268df) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 75), (8, 77), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268e4) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 75), (8, 77), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268e8) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 75), (8, 77), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268ec) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 75), (8, 77), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268ee) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 75), (8, 77), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268f1) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1268a2_1 code

theorem block_l1268a2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1268a2 :=
  Rest.liftedBlock (rest_l1268a2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1268a2 x hx)

theorem rest_l1268f9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1268f9 bytes_l1268f9) (entryMap (live .l1268f9))
      9 0x1268f9 bytes_l1268f9 b_l1268f9 := by
  have f0 : InstrSpec 0x1268f9 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1268f9) (movR64R64Effect 0x1268f9 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1268f9 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1268f9 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1268fc [0x48, 0x81, 0xC4, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1268fc) (addR64Imm32Effect 0x1268fc 4 0x98)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x1268fc 4 0x98).toInstrSpec (add_r64_imm32_effect_step 0x1268fc 0x48 0xc4 0x98 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126903 [0x5B] (PopPre 0x126903) (popR64Effect 0x126903 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126903 1 3).toInstrSpec (pop_r64_effect_step 0x126903 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x126904 [0x41, 0x5C] (PopPre 0x126904) (popR64Effect 0x126904 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126904 2 12).toInstrSpec (pop_r64_rex_effect_step 0x126904 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x126906 [0x41, 0x5D] (PopPre 0x126906) (popR64Effect 0x126906 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126906 2 13).toInstrSpec (pop_r64_rex_effect_step 0x126906 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x126908 [0x41, 0x5E] (PopPre 0x126908) (popR64Effect 0x126908 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126908 2 14).toInstrSpec (pop_r64_rex_effect_step 0x126908 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x12690a [0x41, 0x5F] (PopPre 0x12690a) (popR64Effect 0x12690a 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12690a 2 15).toInstrSpec (pop_r64_rex_effect_step 0x12690a 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x12690c [0x5D] (PopPre 0x12690c) (popR64Effect 0x12690c 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12690c 1 5).toInstrSpec (pop_r64_effect_step 0x12690c 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x12690d [0xC3] (RetPre 0x12690d) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12690d).toInstrSpec (ret_effect_step 0x12690d) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1268fc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126903) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126904) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126906) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126908) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12690a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12690c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12690d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l1268f9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1268f9 :=
  Rest.liftedBlock (rest_l1268f9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1268f9 x hx)

theorem rest_l12690e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12690e bytes_l12690e) (entryMap (live .l12690e))
      10 0x12690e bytes_l12690e b_l12690e := by
  have f0 : InstrSpec 0x12690e [0x41, 0x89, 0x6E, 0x18] (StorePre 0x12690e 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x12690e + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x12690e 5 (.base 14 (.d8 0x18)))
      [.gpr 5, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x12690e 5 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x12690e 0x41 (by decide) 5 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x126912 [0x48, 0x8D, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126912) (leaR64Effect 0x126912 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x126912 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x126912 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12691a [0x49, 0x8B, 0x45, 0x00] (LoadPre 0x12691a (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x12691a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12691a 0 (.base 13 (.d8 0x0)))
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12691a 0 (.base 13 (.d8 0x0))).toInstrSpec (mov_r64_m64_effect_step 0x12691a 0x49 (by decide) 0 (.base 13 (.d8 0x0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12691e [0x49, 0x8B, 0x4D, 0x08] (LoadPre 0x12691e (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x12691e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12691e 1 (.base 13 (.d8 0x8)))
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12691e 1 (.base 13 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12691e 0x49 (by decide) 1 (.base 13 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x126922 [0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x126922 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x126922 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126922 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126922 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x126922 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12692a [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x12692a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x12692a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12692a 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12692a 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x12692a 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x126932 [0x4C, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x126932 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x126932 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126932 14 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126932 14 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x126932 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x12693a [0x48, 0x8D, 0x7C, 0x24, 0x40] (fun s => s.RIP = 0x12693a) (leaR64Effect 0x12693a 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x12693a 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (lea_r64_effect_step 0x12693a 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12693f [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x12693f) (movR64R64Effect 0x12693f 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12693f 6 14).toInstrSpec (mov_r64_r64_effect_step 0x12693f 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x126942 [0xE8, 0x79, 0xDF, 0xFF, 0xFF] (PushPre 0x126942 5) (callEffect (fun _ => 0x1248c0) 0x126947)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x126942 0x1248c0 0x126947).toInstrSpec (call_rel32_effect_step 0x126942 0xffffdf79 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126912) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12691a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12691e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126922) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12692a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126932) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12693a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12693f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126942) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 67), (5, 5), (6, 65), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1248c0) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l12690e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12690e :=
  Rest.liftedBlock (rest_l12690e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12690e x hx)

theorem rest_l126947 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126947 bytes_l126947) (entryMap (live .l126947))
      17 0x126947 bytes_l126947 b_l126947 := by
  have f0 : InstrSpec 0x126947 [0x41, 0x8B, 0x76, 0x18] (LoadPre 0x126947 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126947 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126947 6 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR32M32Effect_footprint 0x126947 6 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x126947 0x41 (by decide) 6 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12694b [0x41, 0x8B, 0x4E, 0x1C] (LoadPre 0x12694b (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x12694b + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x12694b 1 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x12694b 1 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x12694b 0x41 (by decide) 1 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12694f [0x29, 0xCE] (fun s => s.RIP = 0x12694f) (subR32R32Effect 0x12694f 2 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (subR32R32Effect_footprint 0x12694f 2 6 1).toInstrSpec (sub_r32_r32_effect_step 0x12694f 0xce (by decide)) pre_rip
  have f3 : InstrSpec 0x126951 [0x0F, 0x96, 0xC0] (fun s => s.RIP = 0x126951) (atFlags (condHolds 6) (setccR8Effect 0x126951 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x126951 3 0 6).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x126951 6 0xc0 (by decide) (by decide) c)) pre_rip
  have f4 : InstrSpec 0x126954 [0x48, 0x8B, 0x54, 0x24, 0x78] (LoadPre 0x126954 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126954 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126954 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x126954 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x126954 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x126959 [0x49, 0x89, 0x16] (StorePre 0x126959 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126959 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126959 2 (.base 14 .none))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126959 2 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x126959 0x49 (by decide) 2 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x12695c [0x4D, 0x89, 0x66, 0x08] (StorePre 0x12695c 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x12695c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12695c 12 (.base 14 (.d8 0x8)))
      [.gpr 12, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x12695c 12 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x12695c 0x4d (by decide) 4 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x126960 [0x45, 0x89, 0x7E, 0x18] (StorePre 0x126960 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126960 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126960 15 (.base 14 (.d8 0x18)))
      [.gpr 15, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x126960 15 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x126960 0x45 (by decide) 7 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x126964 [0x49, 0x8B, 0x56, 0x10] (LoadPre 0x126964 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126964 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126964 2 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x126964 2 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x126964 0x49 (by decide) 2 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x126968 [0x48, 0x83, 0xFA, 0x01] (fun s => s.RIP = 0x126968) (cmpR64Imm8Effect 0x126968 2 0x1)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x126968 2 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x126968 0x48 0xfa 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x12696c [0x48, 0x83, 0xD2, 0xFF] (fun s => s.RIP = 0x12696c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x12696c 2 0xff))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x12696c 2 0xff).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x12696c 0x48 0xd2 0xff c (by decide) (by decide) (by decide))) pre_rip
  have f11 : InstrSpec 0x126970 [0x49, 0x89, 0x56, 0x10] (StorePre 0x126970 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126970 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126970 2 (.base 14 (.d8 0x10)))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126970 2 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x126970 0x49 (by decide) 2 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x126974 [0x8B, 0x54, 0x24, 0x40] (LoadPre 0x126974 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x126974 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126974 2 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x126974 2 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r32_m32_low_effect_step 0x126974 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x126978 [0x83, 0xFA, 0x02] (fun s => s.RIP = 0x126978) (cmpR32Imm8Effect 0x126978 3 2 0x2)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x126978 3 2 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x126978 0xfa 0x2 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x12697b [0x40, 0x0F, 0x95, 0xC7] (fun s => s.RIP = 0x12697b) (atFlags (condHolds 5) (setccR8Effect 0x12697b 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x12697b 4 7 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x12697b 5 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f15 : InstrSpec 0x12697f [0x40, 0x08, 0xC7] (fun s => s.RIP = 0x12697f) (orR8R8Effect 0x12697f 3 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (orR8R8Effect_footprint 0x12697f 3 7 0).toInstrSpec (or_r8_r8_rex_effect_step 0x12697f 0x40 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (6, 53), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12694b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (6, 53), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12694f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 59) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (6, 57), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126951) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 55), (3, 3), (4, 4), (6, 57), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126954) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 55), (2, 63), (3, 3), (4, 4), (6, 57), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126959) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 61), (1, 55), (2, 63), (3, 3), (4, 4), (6, 57), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12695c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 55), (2, 63), (3, 3), (4, 4), (6, 57), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126960) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 61), (1, 55), (2, 63), (3, 3), (4, 4), (6, 57), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126964) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 61), (1, 55), (2, 68), (3, 3), (4, 4), (6, 57), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126968) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 61), (1, 55), (2, 68), (3, 3), (4, 4), (6, 57), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12696c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 61), (1, 55), (2, 72), (3, 3), (4, 4), (6, 57), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126970) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 61), (1, 55), (2, 72), (3, 3), (4, 4), (6, 57), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126974) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126978) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12697b) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 79), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12697f) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 82) f15 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 83) (ρ' := [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 81), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126982) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 84) (jcc_rel8_effect_step 0x126982 4 0x7c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126947 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126947 :=
  Rest.liftedBlock (rest_l126947 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126947 x hx)

theorem rest_l126984 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126984 bytes_l126984) (entryMap (live .l126984))
      13 0x126984 bytes_l126984 b_l126984 := by
  have f0 : InstrSpec 0x126984 [0x8B, 0x4C, 0x24, 0x44] (LoadPre 0x126984 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x126984 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126984 1 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x126984 1 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_r32_m32_low_effect_step 0x126984 1 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126988 [0x48, 0x8B, 0x44, 0x24, 0x48] (LoadPre 0x126988 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126988 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126988 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126988 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x126988 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12698d [0x48, 0x8B, 0x74, 0x24, 0x50] (LoadPre 0x12698d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x12698d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12698d 6 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12698d 6 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x12698d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126992 [0x48, 0x8B, 0x7C, 0x24, 0x58] (LoadPre 0x126992 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126992 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126992 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126992 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x126992 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x126997 [0x48, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x126997 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126997 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126997 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126997 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x126997 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12699c [0x48, 0x8B, 0x7C, 0x24, 0x60] (LoadPre 0x12699c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12699c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12699c 7 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12699c 7 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x12699c 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1269a1 [0x48, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x1269a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1269a1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1269a1 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1269a1 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1269a1 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1269a6 [0x48, 0x8B, 0x7C, 0x24, 0x68] (LoadPre 0x1269a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1269a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1269a6 7 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1269a6 7 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x1269a6 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1269ab [0x48, 0x89, 0x7C, 0x24, 0x18] (StorePre 0x1269ab 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1269ab + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1269ab 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1269ab 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1269ab 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1269b0 [0x48, 0x8B, 0x7C, 0x24, 0x70] (LoadPre 0x1269b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1269b0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1269b0 7 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1269b0 7 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x1269b0 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1269b5 [0x48, 0x89, 0x7C, 0x24, 0x20] (StorePre 0x1269b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1269b5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1269b5 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1269b5 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1269b5 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1269ba [0x83, 0xFA, 0x02] (fun s => s.RIP = 0x1269ba) (cmpR32Imm8Effect 0x1269ba 3 2 0x2)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1269ba 3 2 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1269ba 0xfa 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126988) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12698d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126992) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126997) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12699c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269a1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269a6) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269ab) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269b0) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269b5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269ba) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269bd) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 73) (jcc_rel32_effect_step 0x1269bd 5 0xfffffea3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126984 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126984 :=
  Rest.liftedBlock (rest_l126984 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126984 x hx)

theorem rest_l1269c3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1269c3 bytes_l1269c3) (entryMap (live .l1269c3))
      14 0x1269c3 bytes_l1269c3 b_l1269c3 := by
  have f0 : InstrSpec 0x1269c3 [0x8B, 0x54, 0x24, 0x18] (LoadPre 0x1269c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1269c3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1269c3 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1269c3 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r32_m32_low_effect_step 0x1269c3 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1269c7 [0x89, 0x54, 0x24, 0x38] (StorePre 0x1269c7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1269c7 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1269c7 2 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1269c7 2 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m32_r32_low_effect_step 0x1269c7 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1269cb [0x48, 0x8B, 0x7C, 0x24, 0x08] (LoadPre 0x1269cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1269cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1269cb 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1269cb 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1269cb 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1269d0 [0x4C, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1269d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1269d0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1269d0 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1269d0 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1269d0 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1269d5 [0x4C, 0x89, 0x44, 0x24, 0x30] (StorePre 0x1269d5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1269d5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1269d5 8 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1269d5 8 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1269d5 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1269da [0x48, 0x89, 0x7C, 0x24, 0x28] (StorePre 0x1269da 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1269da + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1269da 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1269da 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1269da 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1269df [0x89, 0x53, 0x28] (StorePre 0x1269df 3 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1269df + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1269df 2 (.base 3 (.d8 0x28)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1269df 2 (.base 3 (.d8 0x28))).toInstrSpec (mov_m32_r32_low_effect_step 0x1269df 2 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1269e2 [0x4C, 0x89, 0x43, 0x20] (StorePre 0x1269e2 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1269e2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1269e2 8 (.base 3 (.d8 0x20)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1269e2 8 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1269e2 0x4c (by decide) 0 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1269e6 [0x48, 0x89, 0x7B, 0x18] (StorePre 0x1269e6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1269e6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1269e6 7 (.base 3 (.d8 0x18)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1269e6 7 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1269e6 0x48 (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1269ea [0x89, 0x4B, 0x04] (StorePre 0x1269ea 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1269ea + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1269ea 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1269ea 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x1269ea 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1269ed [0x48, 0x89, 0x43, 0x08] (StorePre 0x1269ed 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1269ed + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1269ed 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1269ed 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1269ed 0x48 (by decide) 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1269f1 [0x48, 0x89, 0x73, 0x10] (StorePre 0x1269f1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1269f1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1269f1 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1269f1 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1269f1 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1269f5 [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x1269f5 6 (fun s => AddrMode.addr (.base 3 .none) s (0x1269f5 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x1269f5 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1269f5 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x1269f5 (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269c7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269cb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 56), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269d0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269d5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269da) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269df) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269e2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269e6) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269ea) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269ed) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269f1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269f5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1269fb) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 69) (jmp_rel32_effect_step 0x1269fb 0xfffffef9 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1269c3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1269c3 :=
  Rest.liftedBlock (rest_l1269c3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1269c3 x hx)

theorem rest_l126a00 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126a00 bytes_l126a00) (entryMap (live .l126a00))
      7 0x126a00 bytes_l126a00 b_l126a00 := by
  have f0 : InstrSpec 0x126a00 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x126a00 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x126a00 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x126a00 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x126a00 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x126a00 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x126a05 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x126a05) (movR64R64Effect 0x126a05 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x126a05 0 1).toInstrSpec (mov_r64_r64_effect_step 0x126a05 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126a08 [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x126a08) (shlR64Effect 0x126a08 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x126a08 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x126a08 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x126a0c [0x48, 0x83, 0xC8, 0x13] (fun s => s.RIP = 0x126a0c) (orR64Imm8Effect 0x126a0c 0 0x13)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x126a0c 0 0x13).toInstrSpec (or_r64_imm8_effect_step 0x126a0c 0x48 0xc8 0x13 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x126a10 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126a10) (movR32Imm32Effect 0x126a10 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x126a10 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x126a10 0xba (by decide) 0x1) pre_rip
  have f5 : InstrSpec 0x126a15 [0x31, 0xFF] (fun s => s.RIP = 0x126a15) (xorR32R32Effect 0x126a15 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x126a15 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x126a15 0xff (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a05) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a08) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a0c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a10) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 58), (1, 1), (2, 60), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a15) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 58), (1, 1), (2, 60), (3, 3), (4, 4), (6, 6), (7, 62), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a17) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 64) (jmp_rel32_effect_step 0x126a17 0xfffffe86 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126a00 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126a00 :=
  Rest.liftedBlock (rest_l126a00 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126a00 x hx)

theorem rest_l126a1c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126a1c bytes_l126a1c) (entryMap (live .l126a1c))
      4 0x126a1c bytes_l126a1c b_l126a1c := by
  have f0 : InstrSpec 0x126a1c [0x31, 0xD2] (fun s => s.RIP = 0x126a1c) (xorR32R32Effect 0x126a1c 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x126a1c 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x126a1c 0xd2 (by decide)) pre_rip
  have f1 : InstrSpec 0x126a1e [0xB8, 0x0C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126a1e) (movR32Imm32Effect 0x126a1e 5 0 0xc)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x126a1e 5 0 0xc).toInstrSpec (mov_r32_imm32_effect_step 0x126a1e 0xb8 (by decide) 0xc) pre_rip
  have f2 : InstrSpec 0x126a23 [0x31, 0xFF] (fun s => s.RIP = 0x126a23) (xorR32R32Effect 0x126a23 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x126a23 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x126a23 0xff (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a1e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a23) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a25) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x126a25 0xfffffe78 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126a1c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126a1c :=
  Rest.liftedBlock (rest_l126a1c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126a1c x hx)

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

theorem_by block_l1267c0_eval :
    program.runBlock (dialect code) ⟨.l1267c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1267e4_eval :
    program.runBlock (dialect code) ⟨.l1267e4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126805_eval :
    program.runBlock (dialect code) ⟨.l126805, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12680e_eval :
    program.runBlock (dialect code) ⟨.l12680e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126829_eval :
    program.runBlock (dialect code) ⟨.l126829, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126830_eval :
    program.runBlock (dialect code) ⟨.l126830, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126866_eval :
    program.runBlock (dialect code) ⟨.l126866, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126875_eval :
    program.runBlock (dialect code) ⟨.l126875, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126889_eval :
    program.runBlock (dialect code) ⟨.l126889, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126895_eval :
    program.runBlock (dialect code) ⟨.l126895, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1268a2_eval :
    program.runBlock (dialect code) ⟨.l1268a2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1268f9_eval :
    program.runBlock (dialect code) ⟨.l1268f9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12690e_eval :
    program.runBlock (dialect code) ⟨.l12690e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126947_eval :
    program.runBlock (dialect code) ⟨.l126947, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126984_eval :
    program.runBlock (dialect code) ⟨.l126984, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1269c3_eval :
    program.runBlock (dialect code) ⟨.l1269c3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126a00_eval :
    program.runBlock (dialect code) ⟨.l126a00, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126a1c_eval :
    program.runBlock (dialect code) ⟨.l126a1c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Ecdh.LIR
