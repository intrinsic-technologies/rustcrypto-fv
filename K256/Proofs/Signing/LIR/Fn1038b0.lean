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

theorem rest_l1038b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1038b0 bytes_l1038b0) (entryMap (live .l1038b0))
      12 0x1038b0 bytes_l1038b0 b_l1038b0 := by
  have f0 : InstrSpec 0x1038b0 [0x55] (PushPre 0x1038b0 1) (pushR64Effect 0x1038b0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1038b0 1 5).toInstrSpec (push_r64_effect_step 0x1038b0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1038b1 [0x41, 0x57] (PushPre 0x1038b1 2) (pushR64Effect 0x1038b1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1038b1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1038b1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1038b3 [0x41, 0x56] (PushPre 0x1038b3 2) (pushR64Effect 0x1038b3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1038b3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1038b3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1038b5 [0x41, 0x55] (PushPre 0x1038b5 2) (pushR64Effect 0x1038b5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1038b5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1038b5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1038b7 [0x41, 0x54] (PushPre 0x1038b7 2) (pushR64Effect 0x1038b7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1038b7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1038b7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1038b9 [0x53] (PushPre 0x1038b9 1) (pushR64Effect 0x1038b9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1038b9 1 3).toInstrSpec (push_r64_effect_step 0x1038b9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1038ba [0x48, 0x83, 0xEC, 0x78] (fun s => s.RIP = 0x1038ba) (subR64Imm8Effect 0x1038ba 4 0x78)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1038ba 4 0x78).toInstrSpec (sub_r64_imm8_effect_step 0x1038ba 0x48 0xec 0x78 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1038be [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x1038be) (movR64R64Effect 0x1038be 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1038be 3 7).toInstrSpec (mov_r64_r64_effect_step 0x1038be 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1038c1 [0x44, 0x8B, 0x7E, 0x1C] (LoadPre 0x1038c1 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x1038c1 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1038c1 15 (.base 6 (.d8 0x1c)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x1038c1 15 (.base 6 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x1038c1 0x44 (by decide) 7 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1038c5 [0x8B, 0x6A, 0x08] (LoadPre 0x1038c5 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1038c5 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1038c5 5 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR32M32LowEffect_footprint 0x1038c5 5 (.base 2 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x1038c5 5 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1038c8 [0x44, 0x01, 0xFD] (fun s => s.RIP = 0x1038c8) (addR32R32Effect 0x1038c8 3 5 15)
      [.gpr 5, .gpr 15] [] [.reg 5, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1038c8 3 5 15).toInstrSpec (add_r32_r32_rex_effect_step 0x1038c8 0x44 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038b1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038b3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038b5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038b7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038b9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038ba) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038be) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038c1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038c5) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038c8) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038cb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 76) (jcc_rel32_effect_step 0x1038cb 2 0x1d7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1038b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1038b0 :=
  Rest.liftedBlock (rest_l1038b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1038b0 x hx)

theorem rest_l1038d1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1038d1 bytes_l1038d1) (entryMap (live .l1038d1))
      9 0x1038d1 bytes_l1038d1 b_l1038d1 := by
  have f0 : InstrSpec 0x1038d1 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x1038d1) (movR64R64Effect 0x1038d1 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1038d1 13 2).toInstrSpec (mov_r64_r64_effect_step 0x1038d1 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1038d4 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x1038d4) (movR64R64Effect 0x1038d4 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1038d4 14 6).toInstrSpec (mov_r64_r64_effect_step 0x1038d4 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1038d7 [0x48, 0x8B, 0x36] (LoadPre 0x1038d7 (fun s => AddrMode.addr (.base 6 .none) s (0x1038d7 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1038d7 6 (.base 6 .none))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1038d7 6 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1038d7 0x48 (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1038da [0x4D, 0x8B, 0x66, 0x08] (LoadPre 0x1038da (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1038da + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1038da 12 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x1038da 12 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1038da 0x4d (by decide) 4 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1038de [0x48, 0x8D, 0x7C, 0x24, 0x20] (fun s => s.RIP = 0x1038de) (leaR64Effect 0x1038de 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1038de 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x1038de 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1038e3 [0x48, 0x89, 0x74, 0x24, 0x58] (StorePre 0x1038e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1038e3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1038e3 6 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1038e3 6 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x1038e3 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1038e8 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x1038e8) (movR64R64Effect 0x1038e8 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1038e8 2 12).toInstrSpec (mov_r64_r64_effect_step 0x1038e8 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1038eb [0x89, 0xE9] (fun s => s.RIP = 0x1038eb) (movR32R32Effect 0x1038eb 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1038eb 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x1038eb 0xe9 (by decide)) pre_rip
  have f8 : InstrSpec 0x1038ed [0xE8, 0x5E, 0x43, 0x02, 0x00] (PushPre 0x1038ed 5) (callEffect (fun _ => 0x127c50) 0x1038f2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1038ed 0x127c50 0x1038f2).toInstrSpec (call_rel32_effect_step 0x1038ed 0x2435e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038d4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038d7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038da) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038de) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038e3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038e8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 64), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038eb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038ed) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 68), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c50) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 70) (by decide) (by decide) rfl rfl

theorem block_l1038d1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1038d1 :=
  Rest.liftedBlock (rest_l1038d1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1038d1 x hx)

theorem rest_l1038f2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1038f2 bytes_l1038f2) (entryMap (live .l1038f2))
      3 0x1038f2 bytes_l1038f2 b_l1038f2 := by
  have f0 : InstrSpec 0x1038f2 [0x8B, 0x54, 0x24, 0x20] (LoadPre 0x1038f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1038f2 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1038f2 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1038f2 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r32_m32_low_effect_step 0x1038f2 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1038f6 [0x83, 0xFA, 0x02] (fun s => s.RIP = 0x1038f6) (cmpR32Imm8Effect 0x1038f6 3 2 0x2)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1038f6 3 2 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1038f6 0xfa 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038f6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038f9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1038f9 5 0x22) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1038f2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1038f2 :=
  Rest.liftedBlock (rest_l1038f2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1038f2 x hx)

theorem rest_l1038fb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1038fb bytes_l1038fb) (entryMap (live .l1038fb))
      7 0x1038fb bytes_l1038fb b_l1038fb := by
  have f0 : InstrSpec 0x1038fb [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x1038fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1038fb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1038fb 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1038fb 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1038fb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103900 [0x48, 0x8B, 0x4C, 0x24, 0x30] (LoadPre 0x103900 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x103900 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103900 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x103900 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x103900 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103905 [0x49, 0x89, 0x06] (StorePre 0x103905 3 (fun s => AddrMode.addr (.base 14 .none) s (0x103905 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x103905 0 (.base 14 .none))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x103905 0 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x103905 0x49 (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x103908 [0x49, 0x89, 0x4E, 0x08] (StorePre 0x103908 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x103908 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103908 1 (.base 14 (.d8 0x8)))
      [.gpr 1, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x103908 1 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x103908 0x49 (by decide) 1 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10390c [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x10390c (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x10390c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10390c 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10390c 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10390c 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x103910 [0x48, 0x83, 0xF8, 0x3F] (fun s => s.RIP = 0x103910) (cmpR64Imm8Effect 0x103910 0 0x3f)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x103910 0 0x3f).toInstrSpec (cmp_r64_imm8_effect_step 0x103910 0x48 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103900) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103905) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103908) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10390c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103910) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103914) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x103914 6 0x4b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1038fb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1038fb :=
  Rest.liftedBlock (rest_l1038fb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1038fb x hx)

theorem rest_l103916 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103916 bytes_l103916) (entryMap (live .l103916))
      2 0x103916 bytes_l103916 b_l103916 := by
  have f0 : InstrSpec 0x103916 [0xB8, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103916) (movR32Imm32Effect 0x103916 5 0 0x6)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x103916 5 0 0x6).toInstrSpec (mov_r32_imm32_effect_step 0x103916 0xb8 (by decide) 0x6) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10391b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x10391b 0x60 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103916 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103916 :=
  Rest.liftedBlock (rest_l103916 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103916 x hx)

theorem rest_l10391d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10391d bytes_l10391d) (entryMap (live .l10391d))
      11 0x10391d bytes_l10391d b_l10391d := by
  have f0 : InstrSpec 0x10391d [0x8B, 0x4C, 0x24, 0x24] (LoadPre 0x10391d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x10391d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10391d 1 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x10391d 1 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r32_m32_low_effect_step 0x10391d 1 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103921 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x103921 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x103921 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103921 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103921 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x103921 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103926 [0x48, 0x8B, 0x74, 0x24, 0x30] (LoadPre 0x103926 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x103926 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103926 6 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x103926 6 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x103926 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10392b [0x48, 0x8B, 0x7C, 0x24, 0x38] (LoadPre 0x10392b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10392b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10392b 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10392b 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10392b 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x103930 [0x48, 0x89, 0x3C, 0x24] (StorePre 0x103930 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x103930 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103930 7 (.sib 4 none 0 .none))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103930 7 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x103930 0x48 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x103934 [0x48, 0x8B, 0x7C, 0x24, 0x40] (LoadPre 0x103934 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x103934 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103934 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103934 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x103934 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x103939 [0x48, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x103939 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103939 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103939 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103939 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x103939 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10393e [0x48, 0x8B, 0x7C, 0x24, 0x48] (LoadPre 0x10393e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10393e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10393e 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10393e 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10393e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x103943 [0x48, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x103943 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103943 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103943 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103943 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x103943 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x103948 [0x48, 0x8B, 0x7C, 0x24, 0x50] (LoadPre 0x103948 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x103948 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103948 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103948 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x103948 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x10394d [0x48, 0x89, 0x7C, 0x24, 0x18] (StorePre 0x10394d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10394d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10394d 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10394d 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10394d 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103921) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103926) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10392b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103930) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103934) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103939) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10393e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103943) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103948) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10394d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103952) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 71) (by decide) rfl

theorem block_l10391d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10391d :=
  Rest.liftedBlock (rest_l10391d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10391d x hx)

theorem rest_l103952 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103952 bytes_l103952) (entryMap (live .l103952))
      3 0x103952 bytes_l103952 b_l103952 := by
  have f0 : InstrSpec 0x103952 [0x48, 0xBF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x103952) (movR64Imm64Effect 0x103952 7 0xffffffff00000000)
      [] [] [.reg 7, .rip] :=
    (movR64Imm64Effect_footprint 0x103952 7 0xffffffff00000000).toInstrSpec (mov_r64_imm64_effect_step 0x103952 0x48 0xbf (by decide) (by decide) 0xffffffff00000000) pre_rip
  have f1 : InstrSpec 0x10395c [0x48, 0x21, 0xF7] (fun s => s.RIP = 0x10395c) (andR64R64Effect 0x10395c 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10395c 7 6).toInstrSpec (and_r64_r64_effect_step 0x10395c 0x48 0xf7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10395c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10395f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x10395f 0x29 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103952 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103952 :=
  Rest.liftedBlock (rest_l103952 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103952 x hx)

theorem rest_l103961 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103961 bytes_l103961) (entryMap (live .l103961))
      5 0x103961 bytes_l103961 b_l103961 := by
  have f0 : InstrSpec 0x103961 [0x48, 0xFF, 0xC0] (fun s => s.RIP = 0x103961) (incR64Effect 0x103961 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (incR64Effect_footprint 0x103961 0).toInstrSpec (inc_r64_effect_step 0x103961 0x48 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103964 [0x49, 0x89, 0x46, 0x10] (StorePre 0x103964 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x103964 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103964 0 (.base 14 (.d8 0x10)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x103964 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x103964 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103968 [0x45, 0x8B, 0x7E, 0x18] (LoadPre 0x103968 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x103968 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x103968 15 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x103968 15 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x103968 0x45 (by decide) 7 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10396c [0x44, 0x39, 0xFD] (fun s => s.RIP = 0x10396c) (cmpR32R32Effect 0x10396c 3 5 15)
      [.gpr 5, .gpr 15] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x10396c 3 5 15).toInstrSpec (cmp_r32_r32_rex_effect_step 0x10396c 0x44 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103964) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103968) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10396c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10396f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x10396f 6 0x60) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103961 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103961 :=
  Rest.liftedBlock (rest_l103961 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103961 x hx)

theorem rest_l103971 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103971 bytes_l103971) (entryMap (live .l103971))
      3 0x103971 bytes_l103971 b_l103971 := by
  have f0 : InstrSpec 0x103971 [0x41, 0x8D, 0x47, 0x01] (fun s => s.RIP = 0x103971) (leaR32Effect 0x103971 4 0 (.base 15 (.d8 0x1)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (leaR32Effect_footprint 0x103971 4 0 (.base 15 (.d8 0x1))).toInstrSpec (lea_r32_rex_effect_step 0x103971 0x41 (by decide) 0 (.base 15 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103975 [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x103975) (shlR64Effect 0x103975 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x103975 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x103975 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103979 [0x48, 0x83, 0xC8, 0x03] (fun s => s.RIP = 0x103979) (orR64Imm8Effect 0x103979 0 0x3)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x103979 0 0x3).toInstrSpec (or_r64_imm8_effect_step 0x103979 0x48 0xc8 0x3 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103975) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103979) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10397d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l103971 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103971 :=
  Rest.liftedBlock (rest_l103971 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103971 x hx)

theorem rest_l10397d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10397d bytes_l10397d) (entryMap (live .l10397d))
      4 0x10397d bytes_l10397d b_l10397d := by
  have f0 : InstrSpec 0x10397d [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10397d) (movR32Imm32Effect 0x10397d 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10397d 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x10397d 0xba (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x103982 [0x31, 0xFF] (fun s => s.RIP = 0x103982) (xorR32R32Effect 0x103982 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103982 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x103982 0xff (by decide)) pre_rip
  have f2 : InstrSpec 0x103984 [0x44, 0x89, 0xF9] (fun s => s.RIP = 0x103984) (movR32R32Effect 0x103984 3 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x103984 3 1 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x103984 0x44 0xf9 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103987 [0x44, 0x89, 0xFE] (fun s => s.RIP = 0x103987) (movR32R32Effect 0x103987 3 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x103987 3 6 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x103987 0x44 0xfe (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103982) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (7, 55), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103984) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 53), (3, 3), (4, 4), (7, 55), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103987) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 57), (2, 53), (3, 3), (4, 4), (6, 59), (7, 55), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10398a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l10397d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10397d :=
  Rest.liftedBlock (rest_l10397d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10397d x hx)

theorem rest_l10398a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10398a bytes_l10398a) (entryMap (live .l10398a))
      14 0x10398a bytes_l10398a b_l10398a := by
  have f0 : InstrSpec 0x10398a [0x89, 0xF6] (fun s => s.RIP = 0x10398a) (movR32R32Effect 0x10398a 2 6 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x10398a 2 6 6).toInstrSpec (mov_r32_r32_effect_step 0x10398a 0xf6 (by decide)) pre_rip
  have f1 : InstrSpec 0x10398c [0x48, 0x09, 0xFE] (fun s => s.RIP = 0x10398c) (orR64R64Effect 0x10398c 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10398c 6 7).toInstrSpec (or_r64_r64_effect_step 0x10398c 0x48 0xfe (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10398f [0x48, 0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x10398f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10398f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10398f 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10398f 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10398f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x103994 [0x48, 0x89, 0x7B, 0x30] (StorePre 0x103994 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x103994 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103994 7 (.base 3 (.d8 0x30)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103994 7 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x103994 0x48 (by decide) 7 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x103998 [0x48, 0x8B, 0x7C, 0x24, 0x10] (LoadPre 0x103998 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103998 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103998 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103998 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x103998 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10399d [0x48, 0x89, 0x7B, 0x28] (StorePre 0x10399d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x10399d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10399d 7 (.base 3 (.d8 0x28)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10399d 7 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10399d 0x48 (by decide) 7 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1039a1 [0x48, 0x8B, 0x3C, 0x24] (LoadPre 0x1039a1 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1039a1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1039a1 7 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1039a1 7 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1039a1 0x48 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1039a5 [0x4C, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x1039a5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1039a5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1039a5 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1039a5 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1039a5 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1039aa [0x4C, 0x89, 0x43, 0x20] (StorePre 0x1039aa 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1039aa + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1039aa 8 (.base 3 (.d8 0x20)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1039aa 8 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1039aa 0x4c (by decide) 0 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1039ae [0x48, 0x89, 0x7B, 0x18] (StorePre 0x1039ae 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1039ae + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1039ae 7 (.base 3 (.d8 0x18)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1039ae 7 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1039ae 0x48 (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1039b2 [0x89, 0x13] (StorePre 0x1039b2 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1039b2 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1039b2 2 (.base 3 .none))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1039b2 2 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x1039b2 2 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1039b4 [0x89, 0x4B, 0x04] (StorePre 0x1039b4 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1039b4 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1039b4 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1039b4 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x1039b4 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1039b7 [0x48, 0x89, 0x43, 0x08] (StorePre 0x1039b7 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1039b7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1039b7 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1039b7 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1039b7 0x48 (by decide) 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1039bb [0x48, 0x89, 0x73, 0x10] (StorePre 0x1039bb 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1039bb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1039bb 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1039bb 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1039bb 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10398c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10398f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103994) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103998) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 60), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10399d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 60), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039a1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039a5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039aa) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039ae) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039b2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039b4) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039b7) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039bb) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039bf) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 73) (by decide) rfl

theorem block_l10398a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10398a :=
  Rest.liftedBlock (rest_l10398a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10398a x hx)

theorem rest_l1039bf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1039bf bytes_l1039bf) (entryMap (live .l1039bf))
      9 0x1039bf bytes_l1039bf b_l1039bf := by
  have f0 : InstrSpec 0x1039bf [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1039bf) (movR64R64Effect 0x1039bf 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1039bf 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1039bf 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1039c2 [0x48, 0x83, 0xC4, 0x78] (fun s => s.RIP = 0x1039c2) (addR64Imm8Effect 0x1039c2 4 0x78)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1039c2 4 0x78).toInstrSpec (add_r64_imm8_effect_step 0x1039c2 0x48 0xc4 0x78 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1039c6 [0x5B] (PopPre 0x1039c6) (popR64Effect 0x1039c6 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1039c6 1 3).toInstrSpec (pop_r64_effect_step 0x1039c6 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1039c7 [0x41, 0x5C] (PopPre 0x1039c7) (popR64Effect 0x1039c7 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1039c7 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1039c7 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1039c9 [0x41, 0x5D] (PopPre 0x1039c9) (popR64Effect 0x1039c9 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1039c9 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1039c9 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1039cb [0x41, 0x5E] (PopPre 0x1039cb) (popR64Effect 0x1039cb 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1039cb 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1039cb 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1039cd [0x41, 0x5F] (PopPre 0x1039cd) (popR64Effect 0x1039cd 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1039cd 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1039cd 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1039cf [0x5D] (PopPre 0x1039cf) (popR64Effect 0x1039cf 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1039cf 1 5).toInstrSpec (pop_r64_effect_step 0x1039cf 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x1039d0 [0xC3] (RetPre 0x1039d0) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1039d0).toInstrSpec (ret_effect_step 0x1039d0) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039c2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039c6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039c7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039c9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039cb) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039cd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039cf) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039d0) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l1039bf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1039bf :=
  Rest.liftedBlock (rest_l1039bf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1039bf x hx)

theorem rest_l1039d1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1039d1 bytes_l1039d1) (entryMap (live .l1039d1))
      10 0x1039d1 bytes_l1039d1 b_l1039d1 := by
  have f0 : InstrSpec 0x1039d1 [0x41, 0x89, 0x6E, 0x18] (StorePre 0x1039d1 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1039d1 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1039d1 5 (.base 14 (.d8 0x18)))
      [.gpr 5, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x1039d1 5 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x1039d1 0x41 (by decide) 5 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1039d5 [0x48, 0x8D, 0x54, 0x24, 0x68] (fun s => s.RIP = 0x1039d5) (leaR64Effect 0x1039d5 2 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1039d5 2 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (lea_r64_effect_step 0x1039d5 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1039da [0x49, 0x8B, 0x45, 0x00] (LoadPre 0x1039da (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x1039da + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1039da 0 (.base 13 (.d8 0x0)))
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1039da 0 (.base 13 (.d8 0x0))).toInstrSpec (mov_r64_m64_effect_step 0x1039da 0x49 (by decide) 0 (.base 13 (.d8 0x0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1039de [0x49, 0x8B, 0x4D, 0x08] (LoadPre 0x1039de (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x1039de + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1039de 1 (.base 13 (.d8 0x8)))
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1039de 1 (.base 13 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1039de 0x49 (by decide) 1 (.base 13 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1039e2 [0x48, 0x89, 0x4C, 0x24, 0x70] (StorePre 0x1039e2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1039e2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1039e2 1 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1039e2 1 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x1039e2 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1039e7 [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x1039e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1039e7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1039e7 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1039e7 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x1039e7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1039ec [0x4C, 0x89, 0x74, 0x24, 0x60] (StorePre 0x1039ec 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1039ec + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1039ec 14 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1039ec 14 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x1039ec 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1039f1 [0x48, 0x8D, 0x7C, 0x24, 0x20] (fun s => s.RIP = 0x1039f1) (leaR64Effect 0x1039f1 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1039f1 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x1039f1 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1039f6 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x1039f6) (movR64R64Effect 0x1039f6 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1039f6 6 14).toInstrSpec (mov_r64_r64_effect_step 0x1039f6 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1039f9 [0xE8, 0xF2, 0xC8, 0xFF, 0xFF] (PushPre 0x1039f9 5) (callEffect (fun _ => 0x1002f0) 0x1039fe)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1039f9 0x1002f0 0x1039fe).toInstrSpec (call_rel32_effect_step 0x1039f9 0xffffc8f2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039d5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039da) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039de) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039e2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039e7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039ec) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039f1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039f6) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039f9) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 56), (1, 58), (2, 54), (3, 3), (4, 67), (5, 5), (6, 65), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002f0) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l1039d1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1039d1 :=
  Rest.liftedBlock (rest_l1039d1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1039d1 x hx)

theorem rest_l1039fe [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1039fe bytes_l1039fe) (entryMap (live .l1039fe))
      17 0x1039fe bytes_l1039fe b_l1039fe := by
  have f0 : InstrSpec 0x1039fe [0x41, 0x8B, 0x76, 0x18] (LoadPre 0x1039fe (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1039fe + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1039fe 6 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR32M32Effect_footprint 0x1039fe 6 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x1039fe 0x41 (by decide) 6 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103a02 [0x41, 0x8B, 0x4E, 0x1C] (LoadPre 0x103a02 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x103a02 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x103a02 1 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x103a02 1 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x103a02 0x41 (by decide) 1 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103a06 [0x29, 0xCE] (fun s => s.RIP = 0x103a06) (subR32R32Effect 0x103a06 2 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (subR32R32Effect_footprint 0x103a06 2 6 1).toInstrSpec (sub_r32_r32_effect_step 0x103a06 0xce (by decide)) pre_rip
  have f3 : InstrSpec 0x103a08 [0x0F, 0x96, 0xC0] (fun s => s.RIP = 0x103a08) (atFlags (condHolds 6) (setccR8Effect 0x103a08 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x103a08 3 0 6).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x103a08 6 0xc0 (by decide) (by decide) c)) pre_rip
  have f4 : InstrSpec 0x103a0b [0x48, 0x8B, 0x54, 0x24, 0x58] (LoadPre 0x103a0b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x103a0b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103a0b 2 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x103a0b 2 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x103a0b 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x103a10 [0x49, 0x89, 0x16] (StorePre 0x103a10 3 (fun s => AddrMode.addr (.base 14 .none) s (0x103a10 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x103a10 2 (.base 14 .none))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x103a10 2 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x103a10 0x49 (by decide) 2 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x103a13 [0x4D, 0x89, 0x66, 0x08] (StorePre 0x103a13 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x103a13 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103a13 12 (.base 14 (.d8 0x8)))
      [.gpr 12, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x103a13 12 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x103a13 0x4d (by decide) 4 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x103a17 [0x45, 0x89, 0x7E, 0x18] (StorePre 0x103a17 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x103a17 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x103a17 15 (.base 14 (.d8 0x18)))
      [.gpr 15, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x103a17 15 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x103a17 0x45 (by decide) 7 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x103a1b [0x49, 0x8B, 0x56, 0x10] (LoadPre 0x103a1b (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x103a1b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103a1b 2 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x103a1b 2 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x103a1b 0x49 (by decide) 2 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x103a1f [0x48, 0x83, 0xFA, 0x01] (fun s => s.RIP = 0x103a1f) (cmpR64Imm8Effect 0x103a1f 2 0x1)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x103a1f 2 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x103a1f 0x48 0xfa 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x103a23 [0x48, 0x83, 0xD2, 0xFF] (fun s => s.RIP = 0x103a23) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x103a23 2 0xff))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x103a23 2 0xff).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x103a23 0x48 0xd2 0xff c (by decide) (by decide) (by decide))) pre_rip
  have f11 : InstrSpec 0x103a27 [0x49, 0x89, 0x56, 0x10] (StorePre 0x103a27 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x103a27 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103a27 2 (.base 14 (.d8 0x10)))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x103a27 2 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x103a27 0x49 (by decide) 2 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x103a2b [0x8B, 0x54, 0x24, 0x20] (LoadPre 0x103a2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103a2b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x103a2b 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x103a2b 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r32_m32_low_effect_step 0x103a2b 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x103a2f [0x83, 0xFA, 0x02] (fun s => s.RIP = 0x103a2f) (cmpR32Imm8Effect 0x103a2f 3 2 0x2)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x103a2f 3 2 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x103a2f 0xfa 0x2 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x103a32 [0x40, 0x0F, 0x95, 0xC7] (fun s => s.RIP = 0x103a32) (atFlags (condHolds 5) (setccR8Effect 0x103a32 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x103a32 4 7 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x103a32 5 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f15 : InstrSpec 0x103a36 [0x40, 0x08, 0xC7] (fun s => s.RIP = 0x103a36) (orR8R8Effect 0x103a36 3 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (orR8R8Effect_footprint 0x103a36 3 7 0).toInstrSpec (or_r8_r8_rex_effect_step 0x103a36 0x40 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a02) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a06) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 59) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a08) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 55), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a0b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 55), (2, 63), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a10) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 61), (1, 55), (2, 63), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a13) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 55), (2, 63), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a17) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 61), (1, 55), (2, 63), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a1b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 61), (1, 55), (2, 68), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a1f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 61), (1, 55), (2, 68), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a23) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 61), (1, 55), (2, 72), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a27) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 61), (1, 55), (2, 72), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a2b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a2f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a32) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 79), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a36) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 82) f15 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 83) (ρ' := [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a39) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 84) (jcc_rel8_effect_step 0x103a39 4 0x51) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1039fe [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1039fe :=
  Rest.liftedBlock (rest_l1039fe code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1039fe x hx)

theorem rest_l103a3b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103a3b bytes_l103a3b) (entryMap (live .l103a3b))
      13 0x103a3b bytes_l103a3b b_l103a3b := by
  have f0 : InstrSpec 0x103a3b [0x8B, 0x4C, 0x24, 0x24] (LoadPre 0x103a3b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x103a3b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x103a3b 1 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x103a3b 1 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r32_m32_low_effect_step 0x103a3b 1 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103a3f [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x103a3f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x103a3f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103a3f 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103a3f 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x103a3f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103a44 [0x48, 0x8B, 0x74, 0x24, 0x30] (LoadPre 0x103a44 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x103a44 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103a44 6 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x103a44 6 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x103a44 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x103a49 [0x48, 0x8B, 0x7C, 0x24, 0x38] (LoadPre 0x103a49 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x103a49 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103a49 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103a49 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x103a49 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x103a4e [0x48, 0x89, 0x3C, 0x24] (StorePre 0x103a4e 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x103a4e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103a4e 7 (.sib 4 none 0 .none))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103a4e 7 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x103a4e 0x48 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x103a52 [0x48, 0x8B, 0x7C, 0x24, 0x40] (LoadPre 0x103a52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x103a52 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103a52 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103a52 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x103a52 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x103a57 [0x48, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x103a57 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103a57 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103a57 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103a57 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x103a57 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x103a5c [0x48, 0x8B, 0x7C, 0x24, 0x48] (LoadPre 0x103a5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x103a5c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103a5c 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103a5c 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x103a5c 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x103a61 [0x48, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x103a61 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103a61 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103a61 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103a61 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x103a61 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x103a66 [0x48, 0x8B, 0x7C, 0x24, 0x50] (LoadPre 0x103a66 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x103a66 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103a66 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103a66 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x103a66 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x103a6b [0x48, 0x89, 0x7C, 0x24, 0x18] (StorePre 0x103a6b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103a6b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103a6b 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103a6b 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x103a6b 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x103a70 [0x83, 0xFA, 0x02] (fun s => s.RIP = 0x103a70) (cmpR32Imm8Effect 0x103a70 3 2 0x2)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x103a70 3 2 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x103a70 0xfa 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a3f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a44) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a49) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a4e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a52) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a57) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a5c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a61) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a66) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a6b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a70) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a73) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 73) (jcc_rel32_effect_step 0x103a73 5 0xfffffed9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103a3b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103a3b :=
  Rest.liftedBlock (rest_l103a3b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103a3b x hx)

theorem rest_l103a79 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103a79 bytes_l103a79) (entryMap (live .l103a79))
      4 0x103a79 bytes_l103a79 b_l103a79 := by
  have f0 : InstrSpec 0x103a79 [0x48, 0x89, 0x43, 0x08] (StorePre 0x103a79 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x103a79 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103a79 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103a79 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x103a79 0x48 (by decide) 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x103a7d [0x48, 0x89, 0x73, 0x10] (StorePre 0x103a7d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x103a7d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103a7d 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103a7d 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x103a7d 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103a81 [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x103a81 6 (fun s => AddrMode.addr (.base 3 .none) s (0x103a81 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x103a81 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x103a81 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x103a81 (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a7d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a81) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a87) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 56) (jmp_rel32_effect_step 0x103a87 0xffffff33 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103a79 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103a79 :=
  Rest.liftedBlock (rest_l103a79 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103a79 x hx)

theorem rest_l103a8c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103a8c bytes_l103a8c) (entryMap (live .l103a8c))
      7 0x103a8c bytes_l103a8c b_l103a8c := by
  have f0 : InstrSpec 0x103a8c [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x103a8c 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x103a8c + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x103a8c (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x103a8c (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x103a8c 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x103a91 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x103a91) (movR64R64Effect 0x103a91 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x103a91 0 1).toInstrSpec (mov_r64_r64_effect_step 0x103a91 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103a94 [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x103a94) (shlR64Effect 0x103a94 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x103a94 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x103a94 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103a98 [0x48, 0x83, 0xC8, 0x13] (fun s => s.RIP = 0x103a98) (orR64Imm8Effect 0x103a98 0 0x13)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x103a98 0 0x13).toInstrSpec (or_r64_imm8_effect_step 0x103a98 0x48 0xc8 0x13 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103a9c [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103a9c) (movR32Imm32Effect 0x103a9c 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x103a9c 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x103a9c 0xba (by decide) 0x1) pre_rip
  have f5 : InstrSpec 0x103aa1 [0x31, 0xFF] (fun s => s.RIP = 0x103aa1) (xorR32R32Effect 0x103aa1 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103aa1 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x103aa1 0xff (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a91) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a94) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a98) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a9c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 58), (1, 1), (2, 60), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103aa1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 58), (1, 1), (2, 60), (3, 3), (4, 4), (6, 6), (7, 62), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103aa3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 64) (jmp_rel32_effect_step 0x103aa3 0xfffffee2 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103a8c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103a8c :=
  Rest.liftedBlock (rest_l103a8c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103a8c x hx)

theorem rest_l103aa8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103aa8 bytes_l103aa8) (entryMap (live .l103aa8))
      4 0x103aa8 bytes_l103aa8 b_l103aa8 := by
  have f0 : InstrSpec 0x103aa8 [0x31, 0xD2] (fun s => s.RIP = 0x103aa8) (xorR32R32Effect 0x103aa8 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103aa8 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x103aa8 0xd2 (by decide)) pre_rip
  have f1 : InstrSpec 0x103aaa [0xB8, 0x0C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103aaa) (movR32Imm32Effect 0x103aaa 5 0 0xc)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x103aaa 5 0 0xc).toInstrSpec (mov_r32_imm32_effect_step 0x103aaa 0xb8 (by decide) 0xc) pre_rip
  have f2 : InstrSpec 0x103aaf [0x31, 0xFF] (fun s => s.RIP = 0x103aaf) (xorR32R32Effect 0x103aaf 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103aaf 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x103aaf 0xff (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103aaa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103aaf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ab1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x103ab1 0xfffffed4 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103aa8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103aa8 :=
  Rest.liftedBlock (rest_l103aa8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103aa8 x hx)

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

theorem_by block_l1038b0_eval :
    program.runBlock (dialect code) ⟨.l1038b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1038d1_eval :
    program.runBlock (dialect code) ⟨.l1038d1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1038f2_eval :
    program.runBlock (dialect code) ⟨.l1038f2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1038fb_eval :
    program.runBlock (dialect code) ⟨.l1038fb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103916_eval :
    program.runBlock (dialect code) ⟨.l103916, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10391d_eval :
    program.runBlock (dialect code) ⟨.l10391d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103952_eval :
    program.runBlock (dialect code) ⟨.l103952, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103961_eval :
    program.runBlock (dialect code) ⟨.l103961, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103971_eval :
    program.runBlock (dialect code) ⟨.l103971, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10397d_eval :
    program.runBlock (dialect code) ⟨.l10397d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10398a_eval :
    program.runBlock (dialect code) ⟨.l10398a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1039bf_eval :
    program.runBlock (dialect code) ⟨.l1039bf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1039d1_eval :
    program.runBlock (dialect code) ⟨.l1039d1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1039fe_eval :
    program.runBlock (dialect code) ⟨.l1039fe, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103a3b_eval :
    program.runBlock (dialect code) ⟨.l103a3b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103a79_eval :
    program.runBlock (dialect code) ⟨.l103a79, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103a8c_eval :
    program.runBlock (dialect code) ⟨.l103a8c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103aa8_eval :
    program.runBlock (dialect code) ⟨.l103aa8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
