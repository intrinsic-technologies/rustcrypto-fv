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

theorem rest_l1100a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1100a0 bytes_l1100a0) (entryMap (live .l1100a0))
      12 0x1100a0 bytes_l1100a0 b_l1100a0 := by
  have f0 : InstrSpec 0x1100a0 [0x55] (PushPre 0x1100a0 1) (pushR64Effect 0x1100a0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1100a0 1 5).toInstrSpec (push_r64_effect_step 0x1100a0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1100a1 [0x41, 0x57] (PushPre 0x1100a1 2) (pushR64Effect 0x1100a1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1100a1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1100a1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1100a3 [0x41, 0x56] (PushPre 0x1100a3 2) (pushR64Effect 0x1100a3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1100a3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1100a3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1100a5 [0x41, 0x55] (PushPre 0x1100a5 2) (pushR64Effect 0x1100a5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1100a5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1100a5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1100a7 [0x41, 0x54] (PushPre 0x1100a7 2) (pushR64Effect 0x1100a7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1100a7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1100a7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1100a9 [0x53] (PushPre 0x1100a9 1) (pushR64Effect 0x1100a9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1100a9 1 3).toInstrSpec (push_r64_effect_step 0x1100a9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1100aa [0x48, 0x81, 0xEC, 0xA8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1100aa) (subR64Imm32Effect 0x1100aa 4 0x1a8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x1100aa 4 0x1a8).toInstrSpec (sub_r64_imm32_effect_step 0x1100aa 0x48 0xec 0x1a8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1100b1 [0x49, 0x89, 0xF7] (fun s => s.RIP = 0x1100b1) (movR64R64Effect 0x1100b1 15 6)
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1100b1 15 6).toInstrSpec (mov_r64_r64_effect_step 0x1100b1 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1100b4 [0x48, 0x89, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x1100b4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1100b4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1100b4 7 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1100b4 7 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x1100b4 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1100bc [0x4C, 0x8B, 0x6E, 0x10] (LoadPre 0x1100bc (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1100bc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100bc 13 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x1100bc 13 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1100bc 0x4c (by decide) 5 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1100c0 [0x4D, 0x85, 0xED] (fun s => s.RIP = 0x1100c0) (testR64R64Effect 0x1100c0 13 13)
      [.gpr 13, .gpr 13] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1100c0 13 13).toInstrSpec (test_r64_r64_effect_step 0x1100c0 0x4d 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100a1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100a3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100a5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100a7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100a9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100aa) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100b1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100b4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100bc) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 70), (14, 14), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100c0) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 70), (14, 14), (15, 67), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100c3) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 74) (jcc_rel8_effect_step 0x1100c3 4 0x16) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1100a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1100a0 :=
  Rest.liftedBlock (rest_l1100a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1100a0 x hx)

theorem rest_l1100c5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1100c5 bytes_l1100c5) (entryMap (live .l1100c5))
      6 0x1100c5 bytes_l1100c5 b_l1100c5 := by
  have f0 : InstrSpec 0x1100c5 [0x49, 0x8B, 0x57, 0x18] (LoadPre 0x1100c5 (fun s => AddrMode.addr (.base 15 (.d8 0x18)) s (0x1100c5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100c5 2 (.base 15 (.d8 0x18)))
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1100c5 2 (.base 15 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1100c5 0x49 (by decide) 2 (.base 15 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1100c9 [0x49, 0x8B, 0x4F, 0x20] (LoadPre 0x1100c9 (fun s => AddrMode.addr (.base 15 (.d8 0x20)) s (0x1100c9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100c9 1 (.base 15 (.d8 0x20)))
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1100c9 1 (.base 15 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1100c9 0x49 (by decide) 1 (.base 15 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1100cd [0x49, 0x8B, 0x7F, 0x28] (LoadPre 0x1100cd (fun s => AddrMode.addr (.base 15 (.d8 0x28)) s (0x1100cd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100cd 7 (.base 15 (.d8 0x28)))
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1100cd 7 (.base 15 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1100cd 0x49 (by decide) 7 (.base 15 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1100d1 [0x49, 0x8B, 0x47, 0x30] (LoadPre 0x1100d1 (fun s => AddrMode.addr (.base 15 (.d8 0x30)) s (0x1100d1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100d1 0 (.base 15 (.d8 0x30)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1100d1 0 (.base 15 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1100d1 0x49 (by decide) 0 (.base 15 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1100d5 [0x49, 0x8B, 0x77, 0x38] (LoadPre 0x1100d5 (fun s => AddrMode.addr (.base 15 (.d8 0x38)) s (0x1100d5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100d5 6 (.base 15 (.d8 0x38)))
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1100d5 6 (.base 15 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1100d5 0x49 (by decide) 6 (.base 15 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100c9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (2, 53), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100cd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (2, 53), (3, 3), (4, 4), (7, 57), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100d1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (2, 53), (3, 3), (4, 4), (7, 57), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100d5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 55), (2, 53), (3, 3), (4, 4), (6, 61), (7, 57), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100d9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 63) (jmp_rel8_effect_step 0x1100d9 0x0 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1100c5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1100c5 :=
  Rest.liftedBlock (rest_l1100c5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1100c5 x hx)

theorem rest_l1100db [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1100db bytes_l1100db) (entryMap (live .l1100db))
      6 0x1100db bytes_l1100db b_l1100db := by
  have f0 : InstrSpec 0x1100db [0x48, 0x89, 0x7C, 0x24, 0x18] (StorePre 0x1100db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1100db + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1100db 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1100db 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1100db 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1100e0 [0x49, 0x8B, 0x6F, 0x08] (LoadPre 0x1100e0 (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x1100e0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100e0 5 (.base 15 (.d8 0x8)))
      [.gpr 15] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x1100e0 5 (.base 15 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1100e0 0x49 (by decide) 5 (.base 15 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1100e4 [0x4D, 0x8B, 0x47, 0x40] (LoadPre 0x1100e4 (fun s => AddrMode.addr (.base 15 (.d8 0x40)) s (0x1100e4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100e4 8 (.base 15 (.d8 0x40)))
      [.gpr 15] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1100e4 8 (.base 15 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1100e4 0x4d (by decide) 0 (.base 15 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1100e8 [0x4C, 0x89, 0x04, 0x24] (StorePre 0x1100e8 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1100e8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1100e8 8 (.sib 4 none 0 .none))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1100e8 8 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1100e8 0x4c (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1100ec [0x4D, 0x85, 0xC0] (fun s => s.RIP = 0x1100ec) (testR64R64Effect 0x1100ec 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1100ec 8 8).toInstrSpec (test_r64_r64_effect_step 0x1100ec 0x4d 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100e0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100e4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (7, 7), (8, 56), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100e8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (7, 7), (8, 56), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100ec) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (7, 7), (8, 56), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100ef) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x1100ef 4 0x16) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1100db [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1100db :=
  Rest.liftedBlock (rest_l1100db code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1100db x hx)

theorem rest_l1100f1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1100f1 bytes_l1100f1) (entryMap (live .l1100f1))
      6 0x1100f1 bytes_l1100f1 b_l1100f1 := by
  have f0 : InstrSpec 0x1100f1 [0x4D, 0x8B, 0x5F, 0x48] (LoadPre 0x1100f1 (fun s => AddrMode.addr (.base 15 (.d8 0x48)) s (0x1100f1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100f1 11 (.base 15 (.d8 0x48)))
      [.gpr 15] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1100f1 11 (.base 15 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x1100f1 0x4d (by decide) 3 (.base 15 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1100f5 [0x4D, 0x8B, 0x47, 0x50] (LoadPre 0x1100f5 (fun s => AddrMode.addr (.base 15 (.d8 0x50)) s (0x1100f5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100f5 8 (.base 15 (.d8 0x50)))
      [.gpr 15] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1100f5 8 (.base 15 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x1100f5 0x4d (by decide) 0 (.base 15 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1100f9 [0x49, 0x8B, 0x5F, 0x58] (LoadPre 0x1100f9 (fun s => AddrMode.addr (.base 15 (.d8 0x58)) s (0x1100f9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100f9 3 (.base 15 (.d8 0x58)))
      [.gpr 15] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1100f9 3 (.base 15 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x1100f9 0x49 (by decide) 3 (.base 15 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1100fd [0x4D, 0x8B, 0x4F, 0x60] (LoadPre 0x1100fd (fun s => AddrMode.addr (.base 15 (.d8 0x60)) s (0x1100fd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100fd 9 (.base 15 (.d8 0x60)))
      [.gpr 15] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1100fd 9 (.base 15 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x1100fd 0x4d (by decide) 1 (.base 15 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x110101 [0x4D, 0x8B, 0x57, 0x68] (LoadPre 0x110101 (fun s => AddrMode.addr (.base 15 (.d8 0x68)) s (0x110101 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110101 10 (.base 15 (.d8 0x68)))
      [.gpr 15] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x110101 10 (.base 15 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x110101 0x4d (by decide) 2 (.base 15 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (11, 53), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100f5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (11, 53), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100f9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (11, 53), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100fd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 59), (11, 53), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110101) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 59), (10, 61), (11, 53), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110105) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 63) (jmp_rel8_effect_step 0x110105 0x0 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1100f1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1100f1 :=
  Rest.liftedBlock (rest_l1100f1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1100f1 x hx)

theorem rest_l110107 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110107 bytes_l110107) (entryMap (live .l110107))
      15 0x110107 bytes_l110107 b_l110107 := by
  have f0 : InstrSpec 0x110107 [0x4D, 0x8B, 0x37] (LoadPre 0x110107 (fun s => AddrMode.addr (.base 15 .none) s (0x110107 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x110107 14 (.base 15 .none))
      [.gpr 15] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x110107 14 (.base 15 .none)).toInstrSpec (mov_r64_m64_effect_step 0x110107 0x4d (by decide) 6 (.base 15 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11010a [0x4D, 0x85, 0xED] (fun s => s.RIP = 0x11010a) (testR64R64Effect 0x11010a 13 13)
      [.gpr 13, .gpr 13] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x11010a 13 13).toInstrSpec (test_r64_r64_effect_step 0x11010a 0x4d 0xed (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11010d [0x40, 0x0F, 0x95, 0xC7] (fun s => s.RIP = 0x11010d) (atFlags (condHolds 5) (setccR8Effect 0x11010d 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x11010d 4 7 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11010d 5 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x110111 [0x48, 0x89, 0x6C, 0x24, 0x60] (StorePre 0x110111 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x110111 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110111 5 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110111 5 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x110111 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x110116 [0x4C, 0x8B, 0x24, 0x24] (LoadPre 0x110116 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110116 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110116 12 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x110116 12 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x110116 0x4c (by decide) 4 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x11011a [0x4C, 0x89, 0xA4, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x11011a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11011a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11011a 12 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11011a 12 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x11011a 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x110122 [0x4C, 0x89, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x110122 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x110122 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110122 11 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110122 11 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x110122 0x4c (by decide) 3 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x11012a [0x4C, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x11012a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11012a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11012a 8 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11012a 8 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x11012a 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x110132 [0x48, 0x89, 0x9C, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x110132 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x110132 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110132 3 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110132 3 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x110132 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x11013a [0x4C, 0x89, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x11013a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11013a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11013a 9 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11013a 9 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x11013a 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x110142 [0x4C, 0x89, 0x94, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x110142 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x110142 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110142 10 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110142 10 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x110142 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x11014a [0x48, 0x39, 0xF0] (fun s => s.RIP = 0x11014a) (cmpR64R64Effect 0x11014a 0 6)
      [.gpr 0, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11014a 0 6).toInstrSpec (cmp_r64_r64_effect_step 0x11014a 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11014d [0x41, 0x0F, 0x92, 0xC3] (fun s => s.RIP = 0x11014d) (atFlags (condHolds 2) (setccR8Effect 0x11014d 4 11))
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .rip] :=
    (setccR8Effect_footprint 0x11014d 4 11 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11014d 2 0x41 (by decide) 0xc3 (by decide) c)) pre_rip
  have f13 : InstrSpec 0x110151 [0x44, 0x84, 0xDF] (fun s => s.RIP = 0x110151) (testR8R8Effect 0x110151 3 7 11)
      [.gpr 7, .gpr 11] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x110151 3 7 11).toInstrSpec (test_r8_r8_rex_effect_step 0x110151 0x44 0xdf (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11010a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 53), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11010d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 53), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110111) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 53), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110116) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 53), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11011a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 53), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110122) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 53), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11012a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 53), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110132) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 53), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11013a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 53), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110142) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 53), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11014a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f11 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 53), (15, 15), (16, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11014d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f12 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 70), (12, 60), (13, 13), (14, 53), (15, 15), (16, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110151) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 70), (12, 60), (13, 13), (14, 53), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110154) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 74) (jcc_rel8_effect_step 0x110154 5 0x32) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110107 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110107 :=
  Rest.liftedBlock (rest_l110107 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110107 x hx)

theorem rest_l110156 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110156 bytes_l110156) (entryMap (live .l110156))
      2 0x110156 bytes_l110156 b_l110156 := by
  have f0 : InstrSpec 0x110156 [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x110156) (testR64R64Effect 0x110156 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x110156 14 14).toInstrSpec (test_r64_r64_effect_step 0x110156 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110159) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x110159 4 0x58a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110156 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110156 :=
  Rest.liftedBlock (rest_l110156 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110156 x hx)

theorem rest_l11015f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11015f bytes_l11015f) (entryMap (live .l11015f))
      2 0x11015f bytes_l11015f b_l11015f := by
  have f0 : InstrSpec 0x11015f [0x49, 0x39, 0xEE] (fun s => s.RIP = 0x11015f) (cmpR64R64Effect 0x11015f 14 5)
      [.gpr 14, .gpr 5] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11015f 14 5).toInstrSpec (cmp_r64_r64_effect_step 0x11015f 0x49 0xee (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110162) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x110162 4 0x581) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11015f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11015f :=
  Rest.liftedBlock (rest_l11015f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11015f x hx)

theorem rest_l110168 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110168 bytes_l110168) (entryMap (live .l110168))
      8 0x110168 bytes_l110168 b_l110168 := by
  have f0 : InstrSpec 0x110168 [0x49, 0x8D, 0xBE, 0xA0, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x110168) (leaR64Effect 0x110168 7 (.base 14 (.d32 0x9a0)))
      [.gpr 14] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x110168 7 (.base 14 (.d32 0x9a0))).toInstrSpec (lea_r64_effect_step 0x110168 0x49 (by decide) 7 (.base 14 (.d32 0x9a0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11016f [0x49, 0x8D, 0x8E, 0x80, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x11016f) (leaR64Effect 0x11016f 1 (.base 14 (.d32 0x780)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x11016f 1 (.base 14 (.d32 0x780))).toInstrSpec (lea_r64_effect_step 0x11016f 0x49 (by decide) 1 (.base 14 (.d32 0x780)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x110176 [0xBE, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x110176) (movR32Imm32Effect 0x110176 5 6 0x2)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x110176 5 6 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x110176 0xbe (by decide) 0x2) pre_rip
  have f3 : InstrSpec 0x11017b [0x31, 0xC0] (fun s => s.RIP = 0x11017b) (xorR32R32Effect 0x11017b 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11017b 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x11017b 0xc0 (by decide)) pre_rip
  have f4 : InstrSpec 0x11017d [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x11017d) (movR64R64Effect 0x11017d 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11017d 2 1).toInstrSpec (mov_r64_r64_effect_step 0x11017d 0x48 0xca (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x110180 [0x4D, 0x89, 0xF0] (fun s => s.RIP = 0x110180) (movR64R64Effect 0x110180 8 14)
      [.gpr 14] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x110180 8 14).toInstrSpec (mov_r64_r64_effect_step 0x110180 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x110183 [0x49, 0x89, 0xF9] (fun s => s.RIP = 0x110183) (movR64R64Effect 0x110183 9 7)
      [.gpr 7] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x110183 9 7).toInstrSpec (mov_r64_r64_effect_step 0x110183 0x49 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11016f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110176) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11017b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11017d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110180) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110183) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 63), (9, 65), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110186) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 67) (jmp_rel8_effect_step 0x110186 0xb (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l110168 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110168 :=
  Rest.liftedBlock (rest_l110168 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110168 x hx)

theorem rest_l110188 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110188 bytes_l110188) (entryMap (live .l110188))
      3 0x110188 bytes_l110188 b_l110188 := by
  have f0 : InstrSpec 0x110188 [0x4D, 0x89, 0xE8] (fun s => s.RIP = 0x110188) (movR64R64Effect 0x110188 8 13)
      [.gpr 13] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x110188 8 13).toInstrSpec (mov_r64_r64_effect_step 0x110188 0x4d 0xe8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11018b [0x4D, 0x89, 0xF1] (fun s => s.RIP = 0x11018b) (movR64R64Effect 0x11018b 9 14)
      [.gpr 14] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x11018b 9 14).toInstrSpec (mov_r64_r64_effect_step 0x11018b 0x4d 0xf1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11018e [0x48, 0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x11018e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11018e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11018e 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x11018e 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x11018e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11018b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 53), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11018e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 53), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110193) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l110188 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110188 :=
  Rest.liftedBlock (rest_l110188 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110188 x hx)

theorem rest_l110193 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110193 bytes_l110193) (entryMap (live .l110193))
      10 0x110193 bytes_l110193 b_l110193 := by
  have f0 : InstrSpec 0x110193 [0x48, 0x89, 0x54, 0x24, 0x70] (StorePre 0x110193 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x110193 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110193 2 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110193 2 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x110193 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x110198 [0x48, 0x89, 0x4C, 0x24, 0x78] (StorePre 0x110198 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x110198 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110198 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110198 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x110198 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x11019d [0x48, 0x89, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x11019d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11019d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11019d 7 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11019d 7 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x11019d 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1101a5 [0x48, 0x89, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x1101a5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1101a5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1101a5 6 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1101a5 6 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x1101a5 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1101ad [0x4C, 0x89, 0x44, 0x24, 0x68] (StorePre 0x1101ad 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1101ad + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1101ad 8 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1101ad 8 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x1101ad 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1101b2 [0x4C, 0x89, 0x4C, 0x24, 0x58] (StorePre 0x1101b2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1101b2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1101b2 9 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1101b2 9 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x1101b2 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1101b7 [0x48, 0x8D, 0x50, 0x01] (fun s => s.RIP = 0x1101b7) (leaR64Effect 0x1101b7 2 (.base 0 (.d8 0x1)))
      [.gpr 0] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1101b7 2 (.base 0 (.d8 0x1))).toInstrSpec (lea_r64_effect_step 0x1101b7 0x48 (by decide) 2 (.base 0 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1101bb [0x48, 0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1101bb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1101bb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1101bb 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1101bb 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x1101bb 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1101c3 [0x49, 0x89, 0xC8] (fun s => s.RIP = 0x1101c3) (movR64R64Effect 0x1101c3 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1101c3 8 1).toInstrSpec (mov_r64_r64_effect_step 0x1101c3 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1101c6 [0x49, 0x89, 0xC1] (fun s => s.RIP = 0x1101c6) (movR64R64Effect 0x1101c6 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x1101c6 9 0).toInstrSpec (mov_r64_r64_effect_step 0x1101c6 0x49 0xc1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110198) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11019d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1101a5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1101ad) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1101b2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1101b7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1101bb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1101c3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1101c6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 62), (9, 64), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1101c9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 66) (by decide) rfl

theorem block_l110193 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110193 :=
  Rest.liftedBlock (rest_l110193 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110193 x hx)

theorem rest_l1101c9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1101c9 bytes_l1101c9) (entryMap (live .l1101c9))
      4 0x1101c9 bytes_l1101c9 b_l1101c9 := by
  have f0 : InstrSpec 0x1101c9 [0x49, 0x69, 0xC1, 0x10, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1101c9) (imulR64R64Imm32Effect 0x1101c9 7 0 9 0x110)
      [.gpr 9] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Imm32Effect_footprint 0x1101c9 7 0 9 0x110).toInstrSpec (imul_r64_r64_imm32_effect_step 0x1101c9 0x49 (by decide) 0xc1 (by decide) 0x110) pre_rip
  have f1 : InstrSpec 0x1101d0 [0x49, 0x8B, 0x34, 0x00] (LoadPre 0x1101d0 (fun s => AddrMode.addr (.sib 8 (some 0) 0 .none) s (0x1101d0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1101d0 6 (.sib 8 (some 0) 0 .none))
      [.gpr 8, .gpr 0] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1101d0 6 (.sib 8 (some 0) 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1101d0 0x49 (by decide) 6 (.sib 8 (some 0) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1101d4 [0x48, 0x8D, 0x7C, 0x24, 0x58] (fun s => s.RIP = 0x1101d4) (leaR64Effect 0x1101d4 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1101d4 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (lea_r64_effect_step 0x1101d4 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1101d9 [0xE8, 0xD2, 0xBE, 0x00, 0x00] (PushPre 0x1101d9 5) (callEffect (fun _ => 0x11c0b0) 0x1101de)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1101d9 0x11c0b0 0x1101de).toInstrSpec (call_rel32_effect_step 0x1101d9 0xbed2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1101d0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1101d4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1101d9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (3, 3), (4, 59), (5, 5), (6, 55), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c0b0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1101c9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1101c9 :=
  Rest.liftedBlock (rest_l1101c9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1101c9 x hx)

theorem rest_l1101de [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1101de bytes_l1101de) (entryMap (live .l1101de))
      7 0x1101de bytes_l1101de b_l1101de := by
  have f0 : InstrSpec 0x1101de [0x48, 0x8D, 0xBC, 0x24, 0x30, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1101de) (leaR64Effect 0x1101de 7 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1101de 7 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (lea_r64_effect_step 0x1101de 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1101e6 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1101e6) (movR32Imm32Effect 0x1101e6 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1101e6 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1101e6 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x1101eb [0x48, 0xC7, 0xC6, 0x48, 0x2D, 0x20, 0x00] (fun s => s.RIP = 0x1101eb) (movR64Imm32Effect 0x1101eb 6 0x202d48)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x1101eb 6 0x202d48).toInstrSpec (mov_r64_imm32_effect_step 0x1101eb 0x48 0xc6 (by decide) (by decide) (by decide) 0x202d48) pre_rip
  have f3 : InstrSpec 0x1101f2 [0xF3, 0x48, 0xA5] (RepPre 0x1101f2 (RepMovsqPre 0x1101f2)) (repMovsqEffect 0x1101f2)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1101f2).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1101f2 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x1101f5 [0x48, 0x85, 0xC0] (fun s => s.RIP = 0x1101f5) (testR64R64Effect 0x1101f5 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1101f5 0 0).toInstrSpec (test_r64_r64_effect_step 0x1101f5 0x48 0xc0 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1101f8 [0x4C, 0x8B, 0x04, 0x24] (LoadPre 0x1101f8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1101f8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1101f8 8 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1101f8 8 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1101f8 0x4c (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1101e6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1101eb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1101f2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1101f5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1101f8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (8, 62), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1101fc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel32_effect_step 0x1101fc 4 0x558) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1101de [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1101de :=
  Rest.liftedBlock (rest_l1101de hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1101de x hx)

theorem rest_l110202 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110202 bytes_l110202) (entryMap (live .l110202))
      17 0x110202 bytes_l110202 b_l110202 := by
  have f0 : InstrSpec 0x110202 [0x49, 0x89, 0xC1] (fun s => s.RIP = 0x110202) (movR64R64Effect 0x110202 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x110202 9 0).toInstrSpec (mov_r64_r64_effect_step 0x110202 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110205 [0x49, 0x8B, 0x47, 0x20] (LoadPre 0x110205 (fun s => AddrMode.addr (.base 15 (.d8 0x20)) s (0x110205 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110205 0 (.base 15 (.d8 0x20)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x110205 0 (.base 15 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x110205 0x49 (by decide) 0 (.base 15 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x110209 [0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x110209 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x110209 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110209 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110209 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x110209 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x110211 [0x4D, 0x8B, 0x67, 0x30] (LoadPre 0x110211 (fun s => AddrMode.addr (.base 15 (.d8 0x30)) s (0x110211 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110211 12 (.base 15 (.d8 0x30)))
      [.gpr 15] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x110211 12 (.base 15 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x110211 0x4d (by decide) 4 (.base 15 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x110215 [0x49, 0x8B, 0x47, 0x38] (LoadPre 0x110215 (fun s => AddrMode.addr (.base 15 (.d8 0x38)) s (0x110215 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110215 0 (.base 15 (.d8 0x38)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x110215 0 (.base 15 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x110215 0x49 (by decide) 0 (.base 15 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x110219 [0x48, 0x89, 0x44, 0x24, 0x50] (StorePre 0x110219 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x110219 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110219 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110219 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x110219 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x11021e [0x4D, 0x8B, 0x57, 0x50] (LoadPre 0x11021e (fun s => AddrMode.addr (.base 15 (.d8 0x50)) s (0x11021e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11021e 10 (.base 15 (.d8 0x50)))
      [.gpr 15] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x11021e 10 (.base 15 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x11021e 0x4d (by decide) 2 (.base 15 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x110222 [0x49, 0x8B, 0x47, 0x60] (LoadPre 0x110222 (fun s => AddrMode.addr (.base 15 (.d8 0x60)) s (0x110222 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110222 0 (.base 15 (.d8 0x60)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x110222 0 (.base 15 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x110222 0x49 (by decide) 0 (.base 15 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x110226 [0x48, 0x89, 0x44, 0x24, 0x48] (StorePre 0x110226 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x110226 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110226 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110226 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x110226 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x11022b [0x4D, 0x8B, 0x5F, 0x68] (LoadPre 0x11022b (fun s => AddrMode.addr (.base 15 (.d8 0x68)) s (0x11022b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11022b 11 (.base 15 (.d8 0x68)))
      [.gpr 15] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x11022b 11 (.base 15 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x11022b 0x4d (by decide) 3 (.base 15 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x11022f [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x11022f 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11022f + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11022f (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x11022f (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x11022f 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x110238 [0x4C, 0x89, 0x54, 0x24, 0x08] (StorePre 0x110238 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110238 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110238 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110238 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110238 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x11023d [0x4C, 0x89, 0x6C, 0x24, 0x40] (StorePre 0x11023d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11023d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11023d 13 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11023d 13 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x11023d 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x110242 [0x4C, 0x89, 0x74, 0x24, 0x38] (StorePre 0x110242 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x110242 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110242 14 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110242 14 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x110242 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x110247 [0x4C, 0x89, 0x64, 0x24, 0x30] (StorePre 0x110247 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x110247 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110247 12 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110247 12 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x110247 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x11024c [0x4C, 0x89, 0x5C, 0x24, 0x20] (StorePre 0x11024c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11024c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11024c 11 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11024c 11 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x11024c 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (8, 8), (9, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110205) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (4, 4), (5, 5), (8, 8), (9, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110209) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (2, 2), (4, 4), (5, 5), (8, 8), (9, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110211) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (2, 2), (4, 4), (5, 5), (8, 8), (9, 53), (12, 58), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110215) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (2, 2), (4, 4), (5, 5), (8, 8), (9, 53), (12, 58), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110219) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 60), (2, 2), (4, 4), (5, 5), (8, 8), (9, 53), (12, 58), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11021e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 60), (2, 2), (4, 4), (5, 5), (8, 8), (9, 53), (10, 63), (12, 58), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110222) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (2, 2), (4, 4), (5, 5), (8, 8), (9, 53), (10, 63), (12, 58), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110226) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (2, 2), (4, 4), (5, 5), (8, 8), (9, 53), (10, 63), (12, 58), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11022b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 65), (2, 2), (4, 4), (5, 5), (8, 8), (9, 53), (10, 63), (11, 68), (12, 58), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11022f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 65), (2, 2), (4, 4), (5, 5), (8, 8), (9, 53), (10, 63), (11, 68), (12, 58), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110238) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 65), (2, 2), (4, 4), (5, 5), (8, 8), (9, 53), (10, 63), (11, 68), (12, 58), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11023d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 65), (2, 2), (4, 4), (5, 5), (8, 8), (9, 53), (10, 63), (11, 68), (12, 58), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110242) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 65), (2, 2), (4, 4), (5, 5), (8, 8), (9, 53), (10, 63), (11, 68), (12, 58), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110247) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 65), (2, 2), (4, 4), (5, 5), (8, 8), (9, 53), (10, 63), (11, 68), (12, 58), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11024c) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 65), (2, 2), (4, 4), (5, 5), (8, 8), (9, 53), (10, 63), (11, 68), (12, 58), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110251) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 76) (jmp_rel8_effect_step 0x110251 0x25 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l110202 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110202 :=
  Rest.liftedBlock (rest_l110202 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110202 x hx)

theorem rest_l110260 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110260 bytes_l110260) (entryMap (live .l110260))
      5 0x110260 bytes_l110260 b_l110260 := by
  have f0 : InstrSpec 0x110260 [0x4C, 0x8B, 0x6C, 0x24, 0x40] (LoadPre 0x110260 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x110260 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110260 13 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x110260 13 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x110260 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x110265 [0x4C, 0x8B, 0x74, 0x24, 0x38] (LoadPre 0x110265 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x110265 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110265 14 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x110265 14 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x110265 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11026a [0x4C, 0x8B, 0x64, 0x24, 0x30] (LoadPre 0x11026a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11026a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11026a 12 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x11026a 12 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x11026a 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11026f [0x4D, 0x85, 0xC9] (fun s => s.RIP = 0x11026f) (testR64R64Effect 0x11026f 9 9)
      [.gpr 9, .gpr 9] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x11026f 9 9).toInstrSpec (test_r64_r64_effect_step 0x11026f 0x4d 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110265) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11026a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 53), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11026f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 53), (14, 55), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110272) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel32_effect_step 0x110272 4 0x4e2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110260 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110260 :=
  Rest.liftedBlock (rest_l110260 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110260 x hx)

theorem rest_l110278 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110278 bytes_l110278) (entryMap (live .l110278))
      3 0x110278 bytes_l110278 b_l110278 := by
  have f0 : InstrSpec 0x110278 [0x4C, 0x89, 0xCB] (fun s => s.RIP = 0x110278) (movR64R64Effect 0x110278 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x110278 3 9).toInstrSpec (mov_r64_r64_effect_step 0x110278 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11027b [0xF6, 0x44, 0x24, 0x28, 0x01] (LoadPre 0x11027b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11027b + BitVec.ofNat 64 5)) 1) (testM8Imm8Effect 0x11027b 5 (.sib 4 none 0 (.d8 0x28)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (testM8Imm8Effect_footprint 0x11027b 5 (.sib 4 none 0 (.d8 0x28)) 0x1).toInstrSpec (test_m8_imm8_effect_step 0x11027b (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11027b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110280) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x110280 4 0x40) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110278 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110278 :=
  Rest.liftedBlock (rest_l110278 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110278 x hx)

theorem rest_l110282 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110282 bytes_l110282) (entryMap (live .l110282))
      7 0x110282 bytes_l110282 b_l110282 := by
  have f0 : InstrSpec 0x110282 [0x48, 0x8D, 0x7C, 0x24, 0x58] (fun s => s.RIP = 0x110282) (leaR64Effect 0x110282 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x110282 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (lea_r64_effect_step 0x110282 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110287 [0x4D, 0x89, 0xE7] (fun s => s.RIP = 0x110287) (movR64R64Effect 0x110287 15 12)
      [.gpr 12] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x110287 15 12).toInstrSpec (mov_r64_r64_effect_step 0x110287 0x4d 0xe7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11028a [0x4D, 0x89, 0xF4] (fun s => s.RIP = 0x11028a) (movR64R64Effect 0x11028a 12 14)
      [.gpr 14] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x11028a 12 14).toInstrSpec (mov_r64_r64_effect_step 0x11028a 0x4d 0xf4 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11028d [0x4D, 0x89, 0xEE] (fun s => s.RIP = 0x11028d) (movR64R64Effect 0x11028d 14 13)
      [.gpr 13] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x11028d 14 13).toInstrSpec (mov_r64_r64_effect_step 0x11028d 0x4d 0xee (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x110290 [0x4C, 0x8D, 0xAC, 0x24, 0x30, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x110290) (leaR64Effect 0x110290 13 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x110290 13 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (lea_r64_effect_step 0x110290 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x110298 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x110298) (movR64R64Effect 0x110298 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x110298 6 13).toInstrSpec (mov_r64_r64_effect_step 0x110298 0x4c 0xee (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11029b [0xE8, 0x30, 0x0A, 0x00, 0x00] (PushPre 0x11029b 5) (callEffect (fun _ => 0x110cd0) 0x1102a0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11029b 0x110cd0 0x1102a0).toInstrSpec (call_rel32_effect_step 0x11029b 0xa30 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110287) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11028a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 57), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11028d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 57), (13, 13), (14, 59), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110290) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 57), (13, 61), (14, 59), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110298) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 63), (7, 53), (12, 57), (13, 61), (14, 59), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11029b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 63), (7, 53), (12, 57), (13, 61), (14, 59), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cd0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l110282 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110282 :=
  Rest.liftedBlock (rest_l110282 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110282 x hx)

theorem rest_l1102a0 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1102a0 bytes_l1102a0) (entryMap (live .l1102a0))
      9 0x1102a0 bytes_l1102a0 b_l1102a0 := by
  have f0 : InstrSpec 0x1102a0 [0x4C, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x1102a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1102a0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1102a0 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1102a0 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1102a0 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1102a5 [0x4C, 0x8B, 0x04, 0x24] (LoadPre 0x1102a5 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1102a5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1102a5 8 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1102a5 8 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1102a5 0x4c (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1102a9 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1102a9) (movR32Imm32Effect 0x1102a9 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1102a9 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1102a9 0xb9 (by decide) 0xf) pre_rip
  have f3 : InstrSpec 0x1102ae [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x1102ae) (movR64R64Effect 0x1102ae 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1102ae 7 13).toInstrSpec (mov_r64_r64_effect_step 0x1102ae 0x4c 0xef (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1102b1 [0x4D, 0x89, 0xF5] (fun s => s.RIP = 0x1102b1) (movR64R64Effect 0x1102b1 13 14)
      [.gpr 14] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1102b1 13 14).toInstrSpec (mov_r64_r64_effect_step 0x1102b1 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1102b4 [0x4D, 0x89, 0xE6] (fun s => s.RIP = 0x1102b4) (movR64R64Effect 0x1102b4 14 12)
      [.gpr 12] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1102b4 14 12).toInstrSpec (mov_r64_r64_effect_step 0x1102b4 0x4d 0xe6 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1102b7 [0x4D, 0x89, 0xFC] (fun s => s.RIP = 0x1102b7) (movR64R64Effect 0x1102b7 12 15)
      [.gpr 15] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x1102b7 12 15).toInstrSpec (mov_r64_r64_effect_step 0x1102b7 0x4d 0xfc (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1102ba [0x48, 0x8D, 0x74, 0x24, 0x58] (fun s => s.RIP = 0x1102ba) (leaR64Effect 0x1102ba 6 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1102ba 6 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (lea_r64_effect_step 0x1102ba 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1102bf [0xF3, 0x48, 0xA5] (RepPre 0x1102bf (RepMovsqPre 0x1102bf)) (repMovsqEffect 0x1102bf)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1102bf).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1102bf 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1102a5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 55), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1102a9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (8, 55), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1102ae) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (7, 59), (8, 55), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1102b1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (7, 59), (8, 55), (10, 53), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1102b4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (7, 59), (8, 55), (10, 53), (12, 12), (13, 61), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1102b7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (7, 59), (8, 55), (10, 53), (12, 65), (13, 61), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1102ba) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 67), (7, 59), (8, 55), (10, 53), (12, 65), (13, 61), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1102bf) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 55), (10, 53), (12, 65), (13, 61), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1102c2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 70) (by decide) rfl

theorem block_l1102a0 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1102a0 :=
  Rest.liftedBlock (rest_l1102a0 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1102a0 x hx)

theorem rest_l1102c2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1102c2 bytes_l1102c2) (entryMap (live .l1102c2))
      4 0x1102c2 bytes_l1102c2 b_l1102c2 := by
  have f0 : InstrSpec 0x1102c2 [0x4C, 0x8D, 0x4B, 0xFF] (fun s => s.RIP = 0x1102c2) (leaR64Effect 0x1102c2 9 (.base 3 (.d8 0xff)))
      [.gpr 3] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x1102c2 9 (.base 3 (.d8 0xff))).toInstrSpec (lea_r64_effect_step 0x1102c2 0x4c (by decide) 1 (.base 3 (.d8 0xff)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1102c6 [0x48, 0x81, 0xFB, 0x01, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1102c6) (cmpR64Imm32Effect 0x1102c6 3 0x101)
      [.gpr 3] [] [.flags, .rip] :=
    (cmpR64Imm32Effect_footprint 0x1102c6 3 0x101).toInstrSpec (cmp_r64_imm32_effect_step 0x1102c6 0x48 0xfb 0x101 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1102cd [0x4C, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x1102cd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1102cd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1102cd 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1102cd 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1102cd 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 53), (10, 10), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1102c6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 53), (10, 10), (12, 12), (13, 13), (14, 14), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1102cd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 53), (10, 10), (12, 12), (13, 13), (14, 14), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1102d2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x1102d2 7 0x328) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1102c2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1102c2 :=
  Rest.liftedBlock (rest_l1102c2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1102c2 x hx)

theorem rest_l1102d8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1102d8 bytes_l1102d8) (entryMap (live .l1102d8))
      5 0x1102d8 bytes_l1102d8 b_l1102d8 := by
  have f0 : InstrSpec 0x1102d8 [0x4C, 0x8B, 0x7C, 0x24, 0x48] (LoadPre 0x1102d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1102d8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1102d8 15 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x1102d8 15 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x1102d8 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1102dd [0x48, 0x8B, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x1102dd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1102dd + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1102dd 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1102dd 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x1102dd 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1102e5 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x1102e5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1102e5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1102e5 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1102e5 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1102e5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1102ea [0x48, 0x8B, 0x5C, 0x24, 0x50] (LoadPre 0x1102ea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1102ea + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1102ea 3 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1102ea 3 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x1102ea 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1102dd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1102e5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1102ea) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (2, 2), (3, 58), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1102ef) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 60) (jmp_rel8_effect_step 0x1102ef 0x29 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1102d8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1102d8 :=
  Rest.liftedBlock (rest_l1102d8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1102d8 x hx)

theorem rest_l110300 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110300 bytes_l110300) (entryMap (live .l110300))
      1 0x110300 bytes_l110300 b_l110300 := by
  have f0 : InstrSpec 0x110300 [0xE8, 0x0B, 0xA1, 0xFF, 0xFF] (PushPre 0x110300 5) (callEffect (fun _ => 0x10a410) 0x110305)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x110300 0x10a410 0x110305).toInstrSpec (call_rel32_effect_step 0x110300 0xffffa10b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f0 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 55) (by decide) (by decide) rfl rfl

theorem block_l110300 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110300 :=
  Rest.liftedBlock (rest_l110300 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110300 x hx)

theorem rest_l110305 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110305 bytes_l110305) (entryMap (live .l110305))
      5 0x110305 bytes_l110305 b_l110305 := by
  have f0 : InstrSpec 0x110305 [0xB0, 0x01] (fun s => s.RIP = 0x110305) (movR8Imm8Effect 0x110305 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x110305 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x110305 0xb0 (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x110307 [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x110307 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x110307 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110307 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110307 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x110307 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x11030c [0x4C, 0x8B, 0x04, 0x24] (LoadPre 0x11030c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11030c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11030c 8 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11030c 8 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11030c 0x4c (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x110310 [0x4C, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x110310 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x110310 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110310 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x110310 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x110310 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x110315 [0x4C, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x110315 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110315 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110315 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x110315 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x110315 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110307) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11030c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 56), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110310) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 56), (9, 58), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110315) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 56), (9, 58), (10, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11031a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 62) (by decide) rfl

theorem block_l110305 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110305 :=
  Rest.liftedBlock (rest_l110305 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110305 x hx)

theorem rest_l11031a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11031a bytes_l11031a) (entryMap (live .l11031a))
      3 0x11031a bytes_l11031a b_l11031a := by
  have f0 : InstrSpec 0x11031a [0x4C, 0x8B, 0x5C, 0x24, 0x20] (LoadPre 0x11031a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11031a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11031a 11 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x11031a 11 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x11031a 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11031f [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x11031f) (movR64R64Effect 0x11031f 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11031f 0 15).toInstrSpec (mov_r64_r64_effect_step 0x11031f 0x4c 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11031f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110322) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x110322 0x57 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l11031a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11031a :=
  Rest.liftedBlock (rest_l11031a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11031a x hx)

theorem rest_l110330 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110330 bytes_l110330) (entryMap (live .l110330))
      6 0x110330 bytes_l110330 b_l110330 := by
  have f0 : InstrSpec 0x110330 [0x49, 0x8D, 0x8E, 0x80, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x110330) (leaR64Effect 0x110330 1 (.base 14 (.d32 0x780)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x110330 1 (.base 14 (.d32 0x780))).toInstrSpec (lea_r64_effect_step 0x110330 0x49 (by decide) 1 (.base 14 (.d32 0x780)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110337 [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x110337 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x110337 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110337 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110337 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x110337 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x11033c [0x4D, 0x89, 0xF5] (fun s => s.RIP = 0x11033c) (movR64R64Effect 0x11033c 13 14)
      [.gpr 14] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x11033c 13 14).toInstrSpec (mov_r64_r64_effect_step 0x11033c 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11033f [0x49, 0x81, 0xC6, 0xA0, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x11033f) (addR64Imm32Effect 0x11033f 14 0x9a0)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x11033f 14 0x9a0).toInstrSpec (add_r64_imm32_effect_step 0x11033f 0x49 0xc6 0x9a0 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x110346 [0xBB, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x110346) (movR32Imm32Effect 0x110346 5 3 0x2)
      [] [] [.reg 3, .rip] :=
    (movR32Imm32Effect_footprint 0x110346 5 3 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x110346 0xbb (by decide) 0x2) pre_rip
  have f5 : InstrSpec 0x11034b [0x45, 0x31, 0xE4] (fun s => s.RIP = 0x11034b) (xorR32R32Effect 0x11034b 3 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11034b 3 12 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x11034b 0x45 0xe4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110337) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11033c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 56), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11033f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 56), (14, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110346) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 53), (3, 60), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 56), (14, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11034b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (3, 60), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 62), (13, 56), (14, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11034e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 64) (by decide) rfl

theorem block_l110330 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110330 :=
  Rest.liftedBlock (rest_l110330 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110330 x hx)

theorem rest_l11034e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11034e bytes_l11034e) (entryMap (live .l11034e))
      6 0x11034e bytes_l11034e b_l11034e := by
  have f0 : InstrSpec 0x11034e [0x4C, 0x89, 0xE1] (fun s => s.RIP = 0x11034e) (movR64R64Effect 0x11034e 1 12)
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x11034e 1 12).toInstrSpec (mov_r64_r64_effect_step 0x11034e 0x4c 0xe1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110351 [0x49, 0xFF, 0xC4] (fun s => s.RIP = 0x110351) (incR64Effect 0x110351 12)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (incR64Effect_footprint 0x110351 12).toInstrSpec (inc_r64_effect_step 0x110351 0x49 0xc4 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x110354 [0x48, 0x69, 0xF1, 0xC0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x110354) (imulR64R64Imm32Effect 0x110354 7 6 1 0x3c0)
      [.gpr 1] [] [.reg 6, .flags, .rip] :=
    (imulR64R64Imm32Effect_footprint 0x110354 7 6 1 0x3c0).toInstrSpec (imul_r64_r64_imm32_effect_step 0x110354 0x48 (by decide) 0xf1 (by decide) 0x3c0) pre_rip
  have f3 : InstrSpec 0x11035b [0x4C, 0x01, 0xEE] (fun s => s.RIP = 0x11035b) (addR64R64Effect 0x11035b 6 13)
      [.gpr 6, .gpr 13] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11035b 6 13).toInstrSpec (add_r64_r64_effect_step 0x11035b 0x4c 0xee (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11035e [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x11035e) (movR64R64Effect 0x11035e 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x11035e 15 0).toInstrSpec (mov_r64_r64_effect_step 0x11035e 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x110361 [0x48, 0x8B, 0x54, 0x24, 0x18] (LoadPre 0x110361 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x110361 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110361 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x110361 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x110361 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110351) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110354) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11035b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11035e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110361) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 53), (2, 63), (3, 3), (4, 4), (5, 5), (6, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110366) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 65) (by decide) rfl

theorem block_l11034e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11034e :=
  Rest.liftedBlock (rest_l11034e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11034e x hx)

theorem rest_l110366 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110366 bytes_l110366) (entryMap (live .l110366))
      5 0x110366 bytes_l110366 b_l110366 := by
  have f0 : InstrSpec 0x110366 [0x48, 0x69, 0xC9, 0x10, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x110366) (imulR64R64Imm32Effect 0x110366 7 1 1 0x110)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (imulR64R64Imm32Effect_footprint 0x110366 7 1 1 0x110).toInstrSpec (imul_r64_r64_imm32_effect_step 0x110366 0x48 (by decide) 0xc9 (by decide) 0x110) pre_rip
  have f1 : InstrSpec 0x11036d [0x48, 0x01, 0xD1] (fun s => s.RIP = 0x11036d) (addR64R64Effect 0x11036d 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11036d 1 2).toInstrSpec (add_r64_r64_effect_step 0x11036d 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x110370 [0x41, 0x0F, 0xB6, 0x7C, 0x09, 0x08] (LoadPre 0x110370 (fun s => AddrMode.addr (.sib 9 (some 1) 0 (.d8 0x8)) s (0x110370 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x110370 6 7 (.sib 9 (some 1) 0 (.d8 0x8)))
      [.gpr 9, .gpr 1] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x110370 6 7 (.sib 9 (some 1) 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x110370 0x41 (by decide) 7 (.sib 9 (some 1) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x110376 [0x48, 0x85, 0xFF] (fun s => s.RIP = 0x110376) (testR64R64Effect 0x110376 7 7)
      [.gpr 7, .gpr 7] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x110376 7 7).toInstrSpec (test_r64_r64_effect_step 0x110376 0x48 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11036d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110370) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110376) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110379) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x110379 5 0x45) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110366 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110366 :=
  Rest.liftedBlock (rest_l110366 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110366 x hx)

theorem rest_l11037b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11037b bytes_l11037b) (entryMap (live .l11037b))
      2 0x11037b bytes_l11037b b_l11037b := by
  have f0 : InstrSpec 0x11037b [0x4D, 0x85, 0xED] (fun s => s.RIP = 0x11037b) (testR64R64Effect 0x11037b 13 13)
      [.gpr 13, .gpr 13] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x11037b 13 13).toInstrSpec (test_r64_r64_effect_step 0x11037b 0x4d 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11037e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x11037e 4 0x5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11037b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11037b :=
  Rest.liftedBlock (rest_l11037b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11037b x hx)

theorem rest_l110380 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110380 bytes_l110380) (entryMap (live .l110380))
      2 0x110380 bytes_l110380 b_l110380 := by
  have f0 : InstrSpec 0x110380 [0x49, 0x39, 0xDC] (fun s => s.RIP = 0x110380) (cmpR64R64Effect 0x110380 12 3)
      [.gpr 12, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x110380 12 3).toInstrSpec (cmp_r64_r64_effect_step 0x110380 0x49 0xdc (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110383) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x110383 2 0xc9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110380 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110380 :=
  Rest.liftedBlock (rest_l110380 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110380 x hx)

theorem rest_l110385 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110385 bytes_l110385) (entryMap (live .l110385))
      2 0x110385 bytes_l110385 b_l110385 := by
  have f0 : InstrSpec 0x110385 [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x110385) (testR64R64Effect 0x110385 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x110385 14 14).toInstrSpec (test_r64_r64_effect_step 0x110385 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110388) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x110388 4 0x5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110385 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110385 :=
  Rest.liftedBlock (rest_l110385 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110385 x hx)

theorem rest_l11038a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11038a bytes_l11038a) (entryMap (live .l11038a))
      2 0x11038a bytes_l11038a b_l11038a := by
  have f0 : InstrSpec 0x11038a [0x49, 0x39, 0xEE] (fun s => s.RIP = 0x11038a) (cmpR64R64Effect 0x11038a 14 5)
      [.gpr 14, .gpr 5] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11038a 14 5).toInstrSpec (cmp_r64_r64_effect_step 0x11038a 0x49 0xee (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11038d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x11038d 5 0xa1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11038a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11038a :=
  Rest.liftedBlock (rest_l11038a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11038a x hx)

theorem rest_l11038f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11038f bytes_l11038f) (entryMap (live .l11038f))
      2 0x11038f bytes_l11038f b_l11038f := by
  have f0 : InstrSpec 0x11038f [0x4D, 0x85, 0xC0] (fun s => s.RIP = 0x11038f) (testR64R64Effect 0x11038f 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x11038f 8 8).toInstrSpec (test_r64_r64_effect_step 0x11038f 0x4d 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110392) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x110392 4 0xfffffec8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11038f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11038f :=
  Rest.liftedBlock (rest_l11038f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11038f x hx)

theorem rest_l110398 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110398 bytes_l110398) (entryMap (live .l110398))
      2 0x110398 bytes_l110398 b_l110398 := by
  have f0 : InstrSpec 0x110398 [0x4C, 0x39, 0xD8] (fun s => s.RIP = 0x110398) (cmpR64R64Effect 0x110398 0 11)
      [.gpr 0, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x110398 0 11).toInstrSpec (cmp_r64_r64_effect_step 0x110398 0x4c 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11039b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x11039b 3 0xfffffebf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110398 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110398 :=
  Rest.liftedBlock (rest_l110398 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110398 x hx)

theorem rest_l1103a1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1103a1 bytes_l1103a1) (entryMap (live .l1103a1))
      8 0x1103a1 bytes_l1103a1 b_l1103a1 := by
  have f0 : InstrSpec 0x1103a1 [0x4C, 0x8D, 0x78, 0x01] (fun s => s.RIP = 0x1103a1) (leaR64Effect 0x1103a1 15 (.base 0 (.d8 0x1)))
      [.gpr 0] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x1103a1 15 (.base 0 (.d8 0x1))).toInstrSpec (lea_r64_effect_step 0x1103a1 0x4c (by decide) 7 (.base 0 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1103a5 [0x48, 0x69, 0xF0, 0xC0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x1103a5) (imulR64R64Imm32Effect 0x1103a5 7 6 0 0x3c0)
      [.gpr 0] [] [.reg 6, .flags, .rip] :=
    (imulR64R64Imm32Effect_footprint 0x1103a5 7 6 0 0x3c0).toInstrSpec (imul_r64_r64_imm32_effect_step 0x1103a5 0x48 (by decide) 0xf0 (by decide) 0x3c0) pre_rip
  have f2 : InstrSpec 0x1103ac [0x4C, 0x01, 0xC6] (fun s => s.RIP = 0x1103ac) (addR64R64Effect 0x1103ac 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1103ac 6 8).toInstrSpec (add_r64_r64_effect_step 0x1103ac 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1103af [0x45, 0x31, 0xED] (fun s => s.RIP = 0x1103af) (xorR32R32Effect 0x1103af 3 13 13)
      [.gpr 13, .gpr 13] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1103af 3 13 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x1103af 0x45 0xed (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1103b2 [0x4C, 0x89, 0xD2] (fun s => s.RIP = 0x1103b2) (movR64R64Effect 0x1103b2 2 10)
      [.gpr 10] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1103b2 2 10).toInstrSpec (mov_r64_r64_effect_step 0x1103b2 0x4c 0xd2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1103b5 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x1103b5) (movR64R64Effect 0x1103b5 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1103b5 1 0).toInstrSpec (mov_r64_r64_effect_step 0x1103b5 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1103b8 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x1103b8) (movR64R64Effect 0x1103b8 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1103b8 0 15).toInstrSpec (mov_r64_r64_effect_step 0x1103b8 0x4c 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103a5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103ac) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103af) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103b2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 61), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103b5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 61), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103b8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 63), (2, 61), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103bb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 67) (jmp_rel8_effect_step 0x1103bb 0xa9 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1103a1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1103a1 :=
  Rest.liftedBlock (rest_l1103a1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1103a1 x hx)

theorem rest_l1103c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1103c0 bytes_l1103c0) (entryMap (live .l1103c0))
      3 0x1103c0 bytes_l1103c0 b_l1103c0 := by
  have f0 : InstrSpec 0x1103c0 [0x89, 0xF8] (fun s => s.RIP = 0x1103c0) (movR32R32Effect 0x1103c0 2 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1103c0 2 0 7).toInstrSpec (mov_r32_r32_effect_step 0x1103c0 0xf8 (by decide)) pre_rip
  have f1 : InstrSpec 0x1103c2 [0x40, 0x84, 0xFF] (fun s => s.RIP = 0x1103c2) (testR8R8Effect 0x1103c2 3 7 7)
      [.gpr 7, .gpr 7] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1103c2 3 7 7).toInstrSpec (test_r8_r8_rex_effect_step 0x1103c2 0x40 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103c2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 57) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (20, 56), (21, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103c5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x1103c5 14 0x39) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1103c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1103c0 :=
  Rest.liftedBlock (rest_l1103c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1103c0 x hx)

theorem rest_l1103c7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1103c7 bytes_l1103c7) (entryMap (live .l1103c7))
      3 0x1103c7 bytes_l1103c7 b_l1103c7 := by
  have f0 : InstrSpec 0x1103c7 [0xD1, 0xEF] (fun s => s.RIP = 0x1103c7) (shrR32Effect 0x1103c7 2 7 1)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x1103c7 2 7 1).toInstrSpec (shr_r32_one_effect_step 0x1103c7 0xef (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1103c9 [0x3C, 0x0F] (fun s => s.RIP = 0x1103c9) (cmpAlImm8Effect 0x1103c9 0xf)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x1103c9 0xf).toInstrSpec (cmp_al_imm8_effect_step 0x1103c9 0xf) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103c9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103cb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel32_effect_step 0x1103cb 7 0x3b6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1103c7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1103c7 :=
  Rest.liftedBlock (rest_l1103c7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1103c7 x hx)

theorem rest_l1103d1 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1103d1 bytes_l1103d1) (entryMap (live .l1103d1))
      9 0x1103d1 bytes_l1103d1 b_l1103d1 := by
  have f0 : InstrSpec 0x1103d1 [0x48, 0x6B, 0xC7, 0x78] (fun s => s.RIP = 0x1103d1) (imulR64R64Imm8Effect 0x1103d1 4 0 7 0x78)
      [.gpr 7] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Imm8Effect_footprint 0x1103d1 4 0 7 0x78).toInstrSpec (imul_r64_r64_imm8_effect_step 0x1103d1 0x48 (by decide) 0xc7 (by decide) 0x78) pre_rip
  have f1 : InstrSpec 0x1103d5 [0x48, 0x01, 0xC6] (fun s => s.RIP = 0x1103d5) (addR64R64Effect 0x1103d5 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1103d5 6 0).toInstrSpec (add_r64_r64_effect_step 0x1103d5 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1103d8 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1103d8) (movR32Imm32Effect 0x1103d8 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1103d8 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1103d8 0xb9 (by decide) 0xf) pre_rip
  have f3 : InstrSpec 0x1103dd [0x48, 0x8D, 0x44, 0x24, 0x58] (fun s => s.RIP = 0x1103dd) (leaR64Effect 0x1103dd 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1103dd 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (lea_r64_effect_step 0x1103dd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1103e2 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x1103e2) (movR64R64Effect 0x1103e2 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1103e2 7 0).toInstrSpec (mov_r64_r64_effect_step 0x1103e2 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1103e5 [0xF3, 0x48, 0xA5] (RepPre 0x1103e5 (RepMovsqPre 0x1103e5)) (repMovsqEffect 0x1103e5)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1103e5).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1103e5 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f6 : InstrSpec 0x1103e8 [0x48, 0x8D, 0xBC, 0x24, 0x30, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1103e8) (leaR64Effect 0x1103e8 7 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1103e8 7 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (lea_r64_effect_step 0x1103e8 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1103f0 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x1103f0) (movR64R64Effect 0x1103f0 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1103f0 6 0).toInstrSpec (mov_r64_r64_effect_step 0x1103f0 0x48 0xc6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103d5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103d8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103dd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103e2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103e5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103e8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103f0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (6, 66), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1103f3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 68) (jmp_rel32_effect_step 0x1103f3 0xffffff08 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1103d1 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1103d1 :=
  Rest.liftedBlock (rest_l1103d1 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1103d1 x hx)

theorem rest_l110400 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110400 bytes_l110400) (entryMap (live .l110400))
      7 0x110400 bytes_l110400 b_l110400 := by
  have f0 : InstrSpec 0x110400 [0xF6, 0xD8] (fun s => s.RIP = 0x110400) (negR8Effect 0x110400 2 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR8Effect_footprint 0x110400 2 0).toInstrSpec (neg_r8_effect_step 0x110400 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110402 [0xC0, 0xE8, 0x07] (fun s => s.RIP = 0x110402) (shrR8Effect 0x110402 3 0 7)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR8Effect_footprint 0x110402 3 0 7).toInstrSpec (shr_r8_imm8_effect_step 0x110402 0xe8 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x110405 [0x40, 0x28, 0xF8] (fun s => s.RIP = 0x110405) (subR8R8Effect 0x110405 3 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (subR8R8Effect_footprint 0x110405 3 0 7).toInstrSpec (sub_r8_r8_rex_effect_step 0x110405 0x40 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x110408 [0xD0, 0xF8] (fun s => s.RIP = 0x110408) (sarR8Effect 0x110408 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (sarR8Effect_footprint 0x110408 2 0 1).toInstrSpec (sar_r8_one_effect_step 0x110408 0xf8 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11040a [0x48, 0x0F, 0xBE, 0xF8] (fun s => s.RIP = 0x11040a) (movsxR64R8Effect 0x11040a 4 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movsxR64R8Effect_footprint 0x11040a 4 7 0).toInstrSpec (movsx_r64_r8_effect_step 0x11040a 0x48 (by decide) 0xf8 (by decide)) pre_rip
  have f5 : InstrSpec 0x11040e [0x40, 0x80, 0xFF, 0x07] (fun s => s.RIP = 0x11040e) (cmpR8Imm8Effect 0x11040e 4 7 0x7)
      [.gpr 7] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x11040e 4 7 0x7).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x11040e 0x40 0xff 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110402) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110405) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110408) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11040a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11040e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 61), (12, 12), (13, 13), (14, 14), (15, 15), (16, 63), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110412) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel32_effect_step 0x110412 7 0x380) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110400 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110400 :=
  Rest.liftedBlock (rest_l110400 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110400 x hx)

theorem rest_l110418_4 [Bindings] (code : CodeMap) :
    Rest (n := 188) code lifted (codeRange 0x110418 bytes_l110418) [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 186), (8, 178), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x1105eb bytes_l110418_4 b_l110418_4 := by
  have f80 : InstrSpec 0x1105eb [0x48, 0x8D, 0x74, 0x24, 0x58] (fun s => s.RIP = 0x1105eb) (leaR64Effect 0x1105eb 6 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1105eb 6 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (lea_r64_effect_step 0x1105eb 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 188) (RestInside.out (n := 188) f80 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 189) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 188), (7, 186), (8, 178), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1105f0) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 190) (jmp_rel32_effect_step 0x1105f0 0xfffffd0b (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l110418_3 [Bindings] (code : CodeMap) :
    Rest (n := 160) code lifted (codeRange 0x110418 bytes_l110418) [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 157), (9, 131), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      22 0x110563 bytes_l110418_3 b_l110418_3 := by
  have f60 : InstrSpec 0x110563 [0x4C, 0x8B, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00] (LoadPre 0x110563 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x110563 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110563 8 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x110563 8 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_r64_m64_effect_step 0x110563 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f61 : InstrSpec 0x11056b [0x4C, 0x8B, 0x8C, 0x24, 0xE8, 0x00, 0x00, 0x00] (LoadPre 0x11056b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x11056b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11056b 9 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x11056b 9 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_r64_m64_effect_step 0x11056b 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f62 : InstrSpec 0x110573 [0x4D, 0x89, 0x4A, 0x08] (StorePre 0x110573 4 (fun s => AddrMode.addr (.base 10 (.d8 0x8)) s (0x110573 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110573 9 (.base 10 (.d8 0x8)))
      [.gpr 9, .gpr 10] [] [.rip] :=
    (movM64R64Effect_footprint 0x110573 9 (.base 10 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110573 0x4d (by decide) 1 (.base 10 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f63 : InstrSpec 0x110577 [0x4D, 0x89, 0x02] (StorePre 0x110577 3 (fun s => AddrMode.addr (.base 10 .none) s (0x110577 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x110577 8 (.base 10 .none))
      [.gpr 8, .gpr 10] [] [.rip] :=
    (movM64R64Effect_footprint 0x110577 8 (.base 10 .none)).toInstrSpec (mov_m64_r64_effect_step 0x110577 0x4d (by decide) 0 (.base 10 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f64 : InstrSpec 0x11057a [0x4C, 0x8B, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00] (LoadPre 0x11057a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x11057a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11057a 8 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11057a 8 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_r64_m64_effect_step 0x11057a 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f65 : InstrSpec 0x110582 [0x4C, 0x8B, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00] (LoadPre 0x110582 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x110582 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110582 9 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x110582 9 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_r64_m64_effect_step 0x110582 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f66 : InstrSpec 0x11058a [0x4C, 0x89, 0x44, 0x24, 0x58] (StorePre 0x11058a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11058a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11058a 8 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11058a 8 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x11058a 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f67 : InstrSpec 0x11058f [0x4C, 0x89, 0x4C, 0x24, 0x60] (StorePre 0x11058f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11058f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11058f 9 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11058f 9 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x11058f 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f68 : InstrSpec 0x110594 [0x4C, 0x8B, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00] (LoadPre 0x110594 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x110594 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110594 8 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x110594 8 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_r64_m64_effect_step 0x110594 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f69 : InstrSpec 0x11059c [0x4C, 0x89, 0x44, 0x24, 0x68] (StorePre 0x11059c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11059c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11059c 8 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11059c 8 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x11059c 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f70 : InstrSpec 0x1105a1 [0x4C, 0x8B, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00] (LoadPre 0x1105a1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x1105a1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1105a1 8 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1105a1 8 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_r64_m64_effect_step 0x1105a1 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f71 : InstrSpec 0x1105a9 [0x4C, 0x89, 0x44, 0x24, 0x70] (StorePre 0x1105a9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1105a9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1105a9 8 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1105a9 8 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x1105a9 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f72 : InstrSpec 0x1105ae [0x4C, 0x8B, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00] (LoadPre 0x1105ae (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x1105ae + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1105ae 8 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1105ae 8 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_r64_m64_effect_step 0x1105ae 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f73 : InstrSpec 0x1105b6 [0x4C, 0x89, 0x44, 0x24, 0x78] (StorePre 0x1105b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1105b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1105b6 8 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1105b6 8 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x1105b6 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f74 : InstrSpec 0x1105bb [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x1105bb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1105bb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1105bb 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1105bb 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x1105bb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f75 : InstrSpec 0x1105c3 [0x48, 0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1105c3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1105c3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1105c3 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1105c3 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x1105c3 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f76 : InstrSpec 0x1105cb [0x48, 0x89, 0x94, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x1105cb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1105cb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1105cb 2 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1105cb 2 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x1105cb 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f77 : InstrSpec 0x1105d3 [0x48, 0x89, 0xBC, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x1105d3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1105d3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1105d3 7 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1105d3 7 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x1105d3 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f78 : InstrSpec 0x1105db [0x48, 0x89, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x1105db 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1105db + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1105db 6 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1105db 6 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x1105db 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f79 : InstrSpec 0x1105e3 [0x48, 0x8D, 0xBC, 0x24, 0x30, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1105e3) (leaR64Effect 0x1105e3 7 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1105e3 7 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (lea_r64_effect_step 0x1105e3 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f60 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 160), (9, 131), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11056b) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f61 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 160), (9, 162), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110573) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.exec (n := 164) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 160), (9, 162), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110577) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 165) (RestInside.exec (n := 165) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 160), (9, 162), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11057a) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f64 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 166), (9, 162), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110582) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f65 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 166), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11058a) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.exec (n := 170) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 166), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11058f) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 171) (RestInside.exec (n := 171) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 166), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110594) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f68 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 172), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11059c) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.exec (n := 174) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 172), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1105a1) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f70 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 175), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1105a9) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.exec (n := 177) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 175), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1105ae) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 178) (RestInside.out (n := 178) f72 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 179) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 178), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1105b6) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 180) (RestInside.exec (n := 180) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 178), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1105bb) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 181) (RestInside.exec (n := 181) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 178), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1105c3) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 182) (RestInside.exec (n := 182) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 178), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1105cb) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 183) (RestInside.exec (n := 183) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 178), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1105d3) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 184) (RestInside.exec (n := 184) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 178), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1105db) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 185) (RestInside.exec (n := 185) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 178), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1105e3) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 186) (RestInside.out (n := 186) f79 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 187) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 186), (8, 178), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1105eb) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l110418_4 code

theorem rest_l110418_2 [Bindings] (code : CodeMap) :
    Rest (n := 125) code lifted (codeRange 0x110418 bytes_l110418) [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 123), (7, 110), (8, 72), (9, 53), (10, 121), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      42 0x1104f7 bytes_l110418_2 b_l110418_2 := by
  have f40 : InstrSpec 0x1104f7 [0x48, 0x89, 0xB4, 0x24, 0xE8, 0x00, 0x00, 0x00] (StorePre 0x1104f7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1104f7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1104f7 6 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1104f7 6 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x1104f7 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f41 : InstrSpec 0x1104ff [0x4C, 0x89, 0x94, 0x24, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x1104ff 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1104ff + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1104ff 10 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1104ff 10 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x1104ff 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x110507 [0x48, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00] (fun s => s.RIP = 0x110507) (movR64Imm64Effect 0x110507 6 0xffffffffffff)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x110507 6 0xffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x110507 0x48 0xbe (by decide) (by decide) 0xffffffffffff) pre_rip
  have f43 : InstrSpec 0x110511 [0x49, 0x21, 0xF0] (fun s => s.RIP = 0x110511) (andR64R64Effect 0x110511 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110511 8 6).toInstrSpec (and_r64_r64_effect_step 0x110511 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x110514 [0x49, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x110514) (movR64Imm64Effect 0x110514 9 0xfffffffffffff)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x110514 9 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x110514 0x49 0xb9 (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f45 : InstrSpec 0x11051e [0x4C, 0x21, 0xC8] (fun s => s.RIP = 0x11051e) (andR64R64Effect 0x11051e 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11051e 0 9).toInstrSpec (and_r64_r64_effect_step 0x11051e 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x110521 [0x4C, 0x21, 0xC9] (fun s => s.RIP = 0x110521) (andR64R64Effect 0x110521 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110521 1 9).toInstrSpec (and_r64_r64_effect_step 0x110521 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x110524 [0x4C, 0x01, 0xDF] (fun s => s.RIP = 0x110524) (addR64R64Effect 0x110524 7 11)
      [.gpr 7, .gpr 11] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x110524 7 11).toInstrSpec (add_r64_r64_effect_step 0x110524 0x4c 0xdf (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x110527 [0x4C, 0x21, 0xCA] (fun s => s.RIP = 0x110527) (andR64R64Effect 0x110527 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110527 2 9).toInstrSpec (and_r64_r64_effect_step 0x110527 0x4c 0xca (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x11052a [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x11052a) (movR64R64Effect 0x11052a 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11052a 6 7).toInstrSpec (mov_r64_r64_effect_step 0x11052a 0x48 0xfe (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x11052d [0x48, 0xC1, 0xEE, 0x34] (fun s => s.RIP = 0x11052d) (shrR64Effect 0x11052d 4 6 52)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x11052d 4 6 52).toInstrSpec (shr_r64_imm8_effect_step 0x11052d 0x48 0xee 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x110531 [0x4C, 0x01, 0xC6] (fun s => s.RIP = 0x110531) (addR64R64Effect 0x110531 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x110531 6 8).toInstrSpec (add_r64_r64_effect_step 0x110531 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x110534 [0x4C, 0x21, 0xCF] (fun s => s.RIP = 0x110534) (andR64R64Effect 0x110534 7 9)
      [.gpr 7, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110534 7 9).toInstrSpec (and_r64_r64_effect_step 0x110534 0x4c 0xcf (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x110537 [0x4C, 0x8B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00] (LoadPre 0x110537 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x110537 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110537 8 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x110537 8 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_r64_m64_effect_step 0x110537 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f54 : InstrSpec 0x11053f [0x4C, 0x8D, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11053f) (leaR64Effect 0x11053f 10 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (leaR64Effect_footprint 0x11053f 10 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (lea_r64_effect_step 0x11053f 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x110547 [0x4D, 0x89, 0x42, 0x20] (StorePre 0x110547 4 (fun s => AddrMode.addr (.base 10 (.d8 0x20)) s (0x110547 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110547 8 (.base 10 (.d8 0x20)))
      [.gpr 8, .gpr 10] [] [.rip] :=
    (movM64R64Effect_footprint 0x110547 8 (.base 10 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x110547 0x4d (by decide) 0 (.base 10 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x11054b [0x4C, 0x8B, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00] (LoadPre 0x11054b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x11054b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11054b 8 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11054b 8 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_r64_m64_effect_step 0x11054b 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f57 : InstrSpec 0x110553 [0x4D, 0x89, 0x42, 0x18] (StorePre 0x110553 4 (fun s => AddrMode.addr (.base 10 (.d8 0x18)) s (0x110553 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110553 8 (.base 10 (.d8 0x18)))
      [.gpr 8, .gpr 10] [] [.rip] :=
    (movM64R64Effect_footprint 0x110553 8 (.base 10 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x110553 0x4d (by decide) 0 (.base 10 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f58 : InstrSpec 0x110557 [0x4C, 0x8B, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00] (LoadPre 0x110557 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x110557 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110557 8 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x110557 8 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x110557 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f59 : InstrSpec 0x11055f [0x4D, 0x89, 0x42, 0x10] (StorePre 0x11055f 4 (fun s => AddrMode.addr (.base 10 (.d8 0x10)) s (0x11055f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11055f 8 (.base 10 (.d8 0x10)))
      [.gpr 8, .gpr 10] [] [.rip] :=
    (movM64R64Effect_footprint 0x11055f 8 (.base 10 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x11055f 0x4d (by decide) 0 (.base 10 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 125) (RestInside.exec (n := 125) (ρ' := [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 123), (7, 110), (8, 72), (9, 53), (10, 121), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104ff) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 126) (RestInside.exec (n := 126) (ρ' := [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 123), (7, 110), (8, 72), (9, 53), (10, 121), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110507) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f42 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 127), (7, 110), (8, 72), (9, 53), (10, 121), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110511) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f43 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 127), (7, 110), (8, 129), (9, 53), (10, 121), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110514) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f44 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 127), (7, 110), (8, 129), (9, 131), (10, 121), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11051e) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f45 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 133), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 127), (7, 110), (8, 129), (9, 131), (10, 121), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110521) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 133), (1, 135), (2, 104), (3, 3), (4, 4), (5, 5), (6, 127), (7, 110), (8, 129), (9, 131), (10, 121), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110524) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f47 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 133), (1, 135), (2, 104), (3, 3), (4, 4), (5, 5), (6, 127), (7, 137), (8, 129), (9, 131), (10, 121), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110527) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f48 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 127), (7, 137), (8, 129), (9, 131), (10, 121), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11052a) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f49 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 141), (7, 137), (8, 129), (9, 131), (10, 121), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11052d) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f50 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 143), (7, 137), (8, 129), (9, 131), (10, 121), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110531) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f51 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 137), (8, 129), (9, 131), (10, 121), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110534) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f52 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 129), (9, 131), (10, 121), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110537) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f53 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 149), (9, 131), (10, 121), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11053f) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f54 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 149), (9, 131), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110547) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.exec (n := 153) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 149), (9, 131), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11054b) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f56 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 154), (9, 131), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110553) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.exec (n := 156) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 154), (9, 131), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110557) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f58 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 157), (9, 131), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11055f) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.exec (n := 159) (ρ' := [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 145), (7, 147), (8, 157), (9, 131), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110563) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l110418_3 code

theorem rest_l110418_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x110418 bytes_l110418) [(0, 86), (1, 84), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      62 0x110492 bytes_l110418_1 b_l110418_1 := by
  have f20 : InstrSpec 0x110492 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x110492) (movR64R64Effect 0x110492 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x110492 1 0).toInstrSpec (mov_r64_r64_effect_step 0x110492 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x110495 [0x48, 0xC1, 0xE9, 0x34] (fun s => s.RIP = 0x110495) (shrR64Effect 0x110495 4 1 52)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x110495 4 1 52).toInstrSpec (shr_r64_imm8_effect_step 0x110495 0x48 0xe9 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x110499 [0x4A, 0x2B, 0x4C, 0x0E, 0x30] (LoadPre 0x110499 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x30)) s (0x110499 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110499 1 (.sib 6 (some 9) 0 (.d8 0x30)))
      [.gpr 1, .gpr 6, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x110499 1 (.sib 6 (some 9) 0 (.d8 0x30))).toInstrSpec (sub_r64_m64_effect_step 0x110499 0x4a (by decide) 1 (.sib 6 (some 9) 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x11049e [0x49, 0xBB, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x3F, 0x00] (fun s => s.RIP = 0x11049e) (movR64Imm64Effect 0x11049e 11 0x3ffffffffffffc)
      [] [] [.reg 11, .rip] :=
    (movR64Imm64Effect_footprint 0x11049e 11 0x3ffffffffffffc).toInstrSpec (mov_r64_imm64_effect_step 0x11049e 0x49 0xbb (by decide) (by decide) 0x3ffffffffffffc) pre_rip
  have f24 : InstrSpec 0x1104a8 [0x4C, 0x01, 0xD9] (fun s => s.RIP = 0x1104a8) (addR64R64Effect 0x1104a8 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1104a8 1 11).toInstrSpec (add_r64_r64_effect_step 0x1104a8 0x4c 0xd9 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x1104ab [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x1104ab) (movR64R64Effect 0x1104ab 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1104ab 2 1).toInstrSpec (mov_r64_r64_effect_step 0x1104ab 0x48 0xca (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x1104ae [0x48, 0xC1, 0xEA, 0x34] (fun s => s.RIP = 0x1104ae) (shrR64Effect 0x1104ae 4 2 52)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x1104ae 4 2 52).toInstrSpec (shr_r64_imm8_effect_step 0x1104ae 0x48 0xea 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x1104b2 [0x4A, 0x2B, 0x54, 0x0E, 0x38] (LoadPre 0x1104b2 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x38)) s (0x1104b2 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1104b2 2 (.sib 6 (some 9) 0 (.d8 0x38)))
      [.gpr 2, .gpr 6, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x1104b2 2 (.sib 6 (some 9) 0 (.d8 0x38))).toInstrSpec (sub_r64_m64_effect_step 0x1104b2 0x4a (by decide) 2 (.sib 6 (some 9) 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x1104b7 [0x4C, 0x01, 0xDA] (fun s => s.RIP = 0x1104b7) (addR64R64Effect 0x1104b7 2 11)
      [.gpr 2, .gpr 11] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1104b7 2 11).toInstrSpec (add_r64_r64_effect_step 0x1104b7 0x4c 0xda (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x1104ba [0x48, 0x89, 0xD7] (fun s => s.RIP = 0x1104ba) (movR64R64Effect 0x1104ba 7 2)
      [.gpr 2] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1104ba 7 2).toInstrSpec (mov_r64_r64_effect_step 0x1104ba 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x1104bd [0x48, 0xC1, 0xEF, 0x34] (fun s => s.RIP = 0x1104bd) (shrR64Effect 0x1104bd 4 7 52)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x1104bd 4 7 52).toInstrSpec (shr_r64_imm8_effect_step 0x1104bd 0x48 0xef 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x1104c1 [0x4A, 0x2B, 0x7C, 0x0E, 0x40] (LoadPre 0x1104c1 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x40)) s (0x1104c1 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1104c1 7 (.sib 6 (some 9) 0 (.d8 0x40)))
      [.gpr 7, .gpr 6, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (subR64M64Effect_footprint 0x1104c1 7 (.sib 6 (some 9) 0 (.d8 0x40))).toInstrSpec (sub_r64_m64_effect_step 0x1104c1 0x4a (by decide) 7 (.sib 6 (some 9) 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x1104c6 [0x4E, 0x8B, 0x54, 0x0E, 0x70] (LoadPre 0x1104c6 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x70)) s (0x1104c6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1104c6 10 (.sib 6 (some 9) 0 (.d8 0x70)))
      [.gpr 6, .gpr 9] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1104c6 10 (.sib 6 (some 9) 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x1104c6 0x4e (by decide) 2 (.sib 6 (some 9) 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x1104cb [0x4C, 0x89, 0x94, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x1104cb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x1104cb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1104cb 10 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1104cb 10 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m64_r64_effect_step 0x1104cb 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x1104d3 [0x4E, 0x8B, 0x54, 0x0E, 0x68] (LoadPre 0x1104d3 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x68)) s (0x1104d3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1104d3 10 (.sib 6 (some 9) 0 (.d8 0x68)))
      [.gpr 6, .gpr 9] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1104d3 10 (.sib 6 (some 9) 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x1104d3 0x4e (by decide) 2 (.sib 6 (some 9) 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x1104d8 [0x4C, 0x89, 0x94, 0x24, 0xF8, 0x00, 0x00, 0x00] (StorePre 0x1104d8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x1104d8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1104d8 10 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1104d8 10 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x1104d8 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x1104e0 [0x4E, 0x8B, 0x54, 0x0E, 0x60] (LoadPre 0x1104e0 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x60)) s (0x1104e0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1104e0 10 (.sib 6 (some 9) 0 (.d8 0x60)))
      [.gpr 6, .gpr 9] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1104e0 10 (.sib 6 (some 9) 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x1104e0 0x4e (by decide) 2 (.sib 6 (some 9) 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x1104e5 [0x4C, 0x89, 0x94, 0x24, 0xF0, 0x00, 0x00, 0x00] (StorePre 0x1104e5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x1104e5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1104e5 10 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1104e5 10 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x1104e5 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x1104ed [0x4E, 0x8B, 0x54, 0x0E, 0x50] (LoadPre 0x1104ed (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x50)) s (0x1104ed + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1104ed 10 (.sib 6 (some 9) 0 (.d8 0x50)))
      [.gpr 6, .gpr 9] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1104ed 10 (.sib 6 (some 9) 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x1104ed 0x4e (by decide) 2 (.sib 6 (some 9) 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x1104f2 [0x4A, 0x8B, 0x74, 0x0E, 0x58] (LoadPre 0x1104f2 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x58)) s (0x1104f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1104f2 6 (.sib 6 (some 9) 0 (.d8 0x58)))
      [.gpr 6, .gpr 9] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1104f2 6 (.sib 6 (some 9) 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x1104f2 0x4a (by decide) 6 (.sib 6 (some 9) 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 86), (1, 88), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110495) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 86), (1, 90), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110499) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 86), (1, 92), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11049e) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f23 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 86), (1, 92), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104a8) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 86), (1, 96), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104ab) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f25 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 86), (1, 96), (2, 98), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104ae) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f26 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 86), (1, 96), (2, 100), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104b2) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f27 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 86), (1, 96), (2, 102), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104b7) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f28 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104ba) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f29 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 6), (7, 106), (8, 72), (9, 53), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104bd) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f30 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 6), (7, 108), (8, 72), (9, 53), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104c1) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f31 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 6), (7, 110), (8, 72), (9, 53), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104c6) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f32 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 6), (7, 110), (8, 72), (9, 53), (10, 112), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104cb) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.exec (n := 114) (ρ' := [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 6), (7, 110), (8, 72), (9, 53), (10, 112), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104d3) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f34 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 6), (7, 110), (8, 72), (9, 53), (10, 115), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104d8) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.exec (n := 117) (ρ' := [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 6), (7, 110), (8, 72), (9, 53), (10, 115), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104e0) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f36 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 6), (7, 110), (8, 72), (9, 53), (10, 118), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104e5) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.exec (n := 120) (ρ' := [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 6), (7, 110), (8, 72), (9, 53), (10, 118), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104ed) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f38 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 6), (7, 110), (8, 72), (9, 53), (10, 121), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104f2) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f39 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 86), (1, 96), (2, 104), (3, 3), (4, 4), (5, 5), (6, 123), (7, 110), (8, 72), (9, 53), (10, 121), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1104f7) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l110418_2 code

theorem rest_l110418 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110418 bytes_l110418) (entryMap (live .l110418))
      82 0x110418 bytes_l110418 b_l110418 := by
  have f0 : InstrSpec 0x110418 [0x4C, 0x6B, 0xCF, 0x78] (fun s => s.RIP = 0x110418) (imulR64R64Imm8Effect 0x110418 4 9 7 0x78)
      [.gpr 7] [] [.reg 9, .flags, .rip] :=
    (imulR64R64Imm8Effect_footprint 0x110418 4 9 7 0x78).toInstrSpec (imul_r64_r64_imm8_effect_step 0x110418 0x4c (by decide) 0xcf (by decide) 0x78) pre_rip
  have f1 : InstrSpec 0x11041c [0x4A, 0x8B, 0x44, 0x0E, 0x20] (LoadPre 0x11041c (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x20)) s (0x11041c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11041c 0 (.sib 6 (some 9) 0 (.d8 0x20)))
      [.gpr 6, .gpr 9] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11041c 0 (.sib 6 (some 9) 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x11041c 0x4a (by decide) 0 (.sib 6 (some 9) 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x110421 [0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00] (StorePre 0x110421 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x110421 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110421 0 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110421 0 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_m64_r64_effect_step 0x110421 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x110429 [0x4A, 0x8B, 0x44, 0x0E, 0x18] (LoadPre 0x110429 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x18)) s (0x110429 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110429 0 (.sib 6 (some 9) 0 (.d8 0x18)))
      [.gpr 6, .gpr 9] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x110429 0 (.sib 6 (some 9) 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x110429 0x4a (by decide) 0 (.sib 6 (some 9) 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x11042e [0x48, 0x89, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00] (StorePre 0x11042e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x11042e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11042e 0 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11042e 0 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_m64_r64_effect_step 0x11042e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x110436 [0x4A, 0x8B, 0x44, 0x0E, 0x10] (LoadPre 0x110436 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x10)) s (0x110436 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110436 0 (.sib 6 (some 9) 0 (.d8 0x10)))
      [.gpr 6, .gpr 9] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x110436 0 (.sib 6 (some 9) 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x110436 0x4a (by decide) 0 (.sib 6 (some 9) 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x11043b [0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00] (StorePre 0x11043b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x11043b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11043b 0 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11043b 0 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_m64_r64_effect_step 0x11043b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x110443 [0x4A, 0x8B, 0x04, 0x0E] (LoadPre 0x110443 (fun s => AddrMode.addr (.sib 6 (some 9) 0 .none) s (0x110443 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110443 0 (.sib 6 (some 9) 0 .none))
      [.gpr 6, .gpr 9] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x110443 0 (.sib 6 (some 9) 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x110443 0x4a (by decide) 0 (.sib 6 (some 9) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x110447 [0x4A, 0x8B, 0x4C, 0x0E, 0x08] (LoadPre 0x110447 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x8)) s (0x110447 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110447 1 (.sib 6 (some 9) 0 (.d8 0x8)))
      [.gpr 6, .gpr 9] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x110447 1 (.sib 6 (some 9) 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x110447 0x4a (by decide) 1 (.sib 6 (some 9) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x11044c [0x48, 0x89, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x11044c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x11044c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11044c 1 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11044c 1 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m64_r64_effect_step 0x11044c 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x110454 [0x48, 0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x110454 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x110454 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110454 0 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110454 0 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m64_r64_effect_step 0x110454 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x11045c [0x49, 0xB8, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x00] (fun s => s.RIP = 0x11045c) (movR64Imm64Effect 0x11045c 8 0x3fffffffffffc)
      [] [] [.reg 8, .rip] :=
    (movR64Imm64Effect_footprint 0x11045c 8 0x3fffffffffffc).toInstrSpec (mov_r64_imm64_effect_step 0x11045c 0x49 0xb8 (by decide) (by decide) 0x3fffffffffffc) pre_rip
  have f12 : InstrSpec 0x110466 [0x4E, 0x2B, 0x44, 0x0E, 0x48] (LoadPre 0x110466 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x48)) s (0x110466 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110466 8 (.sib 6 (some 9) 0 (.d8 0x48)))
      [.gpr 8, .gpr 6, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (subR64M64Effect_footprint 0x110466 8 (.sib 6 (some 9) 0 (.d8 0x48))).toInstrSpec (sub_r64_m64_effect_step 0x110466 0x4e (by decide) 0 (.sib 6 (some 9) 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x11046b [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x11046b) (movR64R64Effect 0x11046b 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11046b 0 8).toInstrSpec (mov_r64_r64_effect_step 0x11046b 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x11046e [0x48, 0xC1, 0xE8, 0x30] (fun s => s.RIP = 0x11046e) (shrR64Effect 0x11046e 4 0 48)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x11046e 4 0 48).toInstrSpec (shr_r64_imm8_effect_step 0x11046e 0x48 0xe8 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x110472 [0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x110472) (movR64Imm64Effect 0x110472 1 0x1000003d1)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x110472 1 0x1000003d1).toInstrSpec (mov_r64_imm64_effect_step 0x110472 0x48 0xb9 (by decide) (by decide) 0x1000003d1) pre_rip
  have f16 : InstrSpec 0x11047c [0x48, 0x0F, 0xAF, 0xC1] (fun s => s.RIP = 0x11047c) (imulR64R64Effect 0x11047c 4 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x11047c 4 0 1).toInstrSpec (imul_r64_r64_effect_step 0x11047c 0x48 (by decide) 0xc1 (by decide)) pre_rip
  have f17 : InstrSpec 0x110480 [0x4A, 0x2B, 0x44, 0x0E, 0x28] (LoadPre 0x110480 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x28)) s (0x110480 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110480 0 (.sib 6 (some 9) 0 (.d8 0x28)))
      [.gpr 0, .gpr 6, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (subR64M64Effect_footprint 0x110480 0 (.sib 6 (some 9) 0 (.d8 0x28))).toInstrSpec (sub_r64_m64_effect_step 0x110480 0x4a (by decide) 0 (.sib 6 (some 9) 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x110485 [0x48, 0xB9, 0xBC, 0xF0, 0xFF, 0xFF, 0xFB, 0xFF, 0x3F, 0x00] (fun s => s.RIP = 0x110485) (movR64Imm64Effect 0x110485 1 0x3ffffbfffff0bc)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x110485 1 0x3ffffbfffff0bc).toInstrSpec (mov_r64_imm64_effect_step 0x110485 0x48 0xb9 (by decide) (by decide) 0x3ffffbfffff0bc) pre_rip
  have f19 : InstrSpec 0x11048f [0x48, 0x01, 0xC8] (fun s => s.RIP = 0x11048f) (addR64R64Effect 0x11048f 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11048f 0 1).toInstrSpec (add_r64_r64_effect_step 0x11048f 0x48 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11041c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110421) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110429) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11042e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110436) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11043b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110443) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110447) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11044c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110454) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11045c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 70), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110466) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11046b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 66), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11046e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 66), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110472) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 76), (1, 78), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11047c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 78), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110480) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 82), (1, 78), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110485) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 82), (1, 84), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11048f) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 86), (1, 84), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110492) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l110418_1 code

theorem block_l110418 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110418 :=
  Rest.liftedBlock (rest_l110418 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110418 x hx)

theorem rest_l110600 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110600 bytes_l110600) (entryMap (live .l110600))
      12 0x110600 bytes_l110600 b_l110600 := by
  have f0 : InstrSpec 0x110600 [0x48, 0x8B, 0x54, 0x24, 0x50] (LoadPre 0x110600 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x110600 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110600 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x110600 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x110600 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x110605 [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x110605) (movR64R64Effect 0x110605 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x110605 9 2).toInstrSpec (mov_r64_r64_effect_step 0x110605 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x110608 [0x4D, 0x89, 0xE3] (fun s => s.RIP = 0x110608) (movR64R64Effect 0x110608 11 12)
      [.gpr 12] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x110608 11 12).toInstrSpec (mov_r64_r64_effect_step 0x110608 0x4d 0xe3 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11060b [0x4D, 0x89, 0xEA] (fun s => s.RIP = 0x11060b) (movR64R64Effect 0x11060b 10 13)
      [.gpr 13] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x11060b 10 13).toInstrSpec (mov_r64_r64_effect_step 0x11060b 0x4d 0xea (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11060e [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11060e) (movR64R64Effect 0x11060e 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11060e 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11060e 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x110611 [0x48, 0x8B, 0x44, 0x24, 0x48] (LoadPre 0x110611 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x110611 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110611 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x110611 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x110611 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x110616 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x110616) (movR64R64Effect 0x110616 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x110616 6 12).toInstrSpec (mov_r64_r64_effect_step 0x110616 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x110619 [0x4C, 0x89, 0xC3] (fun s => s.RIP = 0x110619) (movR64R64Effect 0x110619 3 8)
      [.gpr 8] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x110619 3 8).toInstrSpec (mov_r64_r64_effect_step 0x110619 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11061c [0x4D, 0x89, 0xE8] (fun s => s.RIP = 0x11061c) (movR64R64Effect 0x11061c 8 13)
      [.gpr 13] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x11061c 8 13).toInstrSpec (mov_r64_r64_effect_step 0x11061c 0x4d 0xe8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11061f [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x11061f) (movR64R64Effect 0x11061f 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x11061f 1 14).toInstrSpec (mov_r64_r64_effect_step 0x11061f 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x110622 [0x48, 0x85, 0xDB] (fun s => s.RIP = 0x110622) (testR64R64Effect 0x110622 3 3)
      [.gpr 3, .gpr 3] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x110622 3 3).toInstrSpec (test_r64_r64_effect_step 0x110622 0x48 0xdb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (4, 4), (5, 5), (8, 8), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110605) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (4, 4), (5, 5), (8, 8), (9, 55), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110608) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 53), (4, 4), (5, 5), (8, 8), (9, 55), (11, 57), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11060b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 53), (4, 4), (5, 5), (8, 8), (9, 55), (10, 59), (11, 57), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11060e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 53), (4, 4), (5, 5), (7, 61), (8, 8), (9, 55), (10, 59), (11, 57), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110611) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (2, 53), (4, 4), (5, 5), (7, 61), (8, 8), (9, 55), (10, 59), (11, 57), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110616) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 63), (2, 53), (4, 4), (5, 5), (6, 65), (7, 61), (8, 8), (9, 55), (10, 59), (11, 57), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110619) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 63), (2, 53), (3, 67), (4, 4), (5, 5), (6, 65), (7, 61), (8, 8), (9, 55), (10, 59), (11, 57), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11061c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 63), (2, 53), (3, 67), (4, 4), (5, 5), (6, 65), (7, 61), (8, 69), (9, 55), (10, 59), (11, 57), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11061f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 63), (1, 71), (2, 53), (3, 67), (4, 4), (5, 5), (6, 65), (7, 61), (8, 69), (9, 55), (10, 59), (11, 57), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110622) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 63), (1, 71), (2, 53), (3, 67), (4, 4), (5, 5), (6, 65), (7, 61), (8, 69), (9, 55), (10, 59), (11, 57), (12, 12), (13, 13), (14, 14), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110625) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 75) (jcc_rel32_effect_step 0x110625 4 0x8b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110600 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110600 :=
  Rest.liftedBlock (rest_l110600 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110600 x hx)

theorem rest_l11062b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11062b bytes_l11062b) (entryMap (live .l11062b))
      4 0x11062b bytes_l11062b b_l11062b := by
  have f0 : InstrSpec 0x11062b [0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x11062b) (fun _ => nopEffect 0x11062b 5)
      [] [] [.rip] :=
    (nopEffect_footprint 0x11062b 5).toInstrSpec (nop_m_effect_step 0x11062b [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110630 [0x4C, 0x8B, 0x5C, 0x24, 0x20] (LoadPre 0x110630 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x110630 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110630 11 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x110630 11 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x110630 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x110635 [0x4D, 0x85, 0xC0] (fun s => s.RIP = 0x110635) (testR64R64Effect 0x110635 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x110635 8 8).toInstrSpec (test_r64_r64_effect_step 0x110635 0x4d 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110630) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (11, 54), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110635) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (11, 54), (12, 12), (13, 13), (14, 14), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110638) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x110638 5 0xe) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11062b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11062b :=
  Rest.liftedBlock (rest_l11062b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11062b x hx)

theorem rest_l11063a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11063a bytes_l11063a) (entryMap (live .l11063a))
      1 0x11063a bytes_l11063a b_l11063a := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x11063a 0x11 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l11063a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11063a :=
  Rest.liftedBlock (rest_l11063a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11063a x hx)

theorem rest_l110640 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110640 bytes_l110640) (entryMap (live .l110640))
      3 0x110640 bytes_l110640 b_l110640 := by
  have f0 : InstrSpec 0x110640 [0x48, 0xFF, 0xC6] (fun s => s.RIP = 0x110640) (incR64Effect 0x110640 6)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (incR64Effect_footprint 0x110640 6).toInstrSpec (inc_r64_effect_step 0x110640 0x48 0xc6 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110643 [0x4D, 0x85, 0xC0] (fun s => s.RIP = 0x110643) (testR64R64Effect 0x110643 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x110643 8 8).toInstrSpec (test_r64_r64_effect_step 0x110643 0x4d 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110643) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110646) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x110646 4 0x5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110640 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110640 :=
  Rest.liftedBlock (rest_l110640 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110640 x hx)

theorem rest_l110648 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110648 bytes_l110648) (entryMap (live .l110648))
      2 0x110648 bytes_l110648 b_l110648 := by
  have f0 : InstrSpec 0x110648 [0x48, 0x39, 0xD6] (fun s => s.RIP = 0x110648) (cmpR64R64Effect 0x110648 6 2)
      [.gpr 6, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x110648 6 2).toInstrSpec (cmp_r64_r64_effect_step 0x110648 0x48 0xd6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11064b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x11064b 2 0xf3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110648 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110648 :=
  Rest.liftedBlock (rest_l110648 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110648 x hx)

theorem rest_l11064d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11064d bytes_l11064d) (entryMap (live .l11064d))
      2 0x11064d bytes_l11064d b_l11064d := by
  have f0 : InstrSpec 0x11064d [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x11064d) (testR64R64Effect 0x11064d 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x11064d 1 1).toInstrSpec (test_r64_r64_effect_step 0x11064d 0x48 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110650) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x110650 4 0x2e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11064d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11064d :=
  Rest.liftedBlock (rest_l11064d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11064d x hx)

theorem rest_l110652 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110652 bytes_l110652) (entryMap (live .l110652))
      2 0x110652 bytes_l110652 b_l110652 := by
  have f0 : InstrSpec 0x110652 [0x48, 0x39, 0xE9] (fun s => s.RIP = 0x110652) (cmpR64R64Effect 0x110652 1 5)
      [.gpr 1, .gpr 5] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x110652 1 5).toInstrSpec (cmp_r64_r64_effect_step 0x110652 0x48 0xe9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110655) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x110655 4 0x29) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110652 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110652 :=
  Rest.liftedBlock (rest_l110652 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110652 x hx)

theorem rest_l110657 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110657 bytes_l110657) (entryMap (live .l110657))
      7 0x110657 bytes_l110657 b_l110657 := by
  have f0 : InstrSpec 0x110657 [0x49, 0x89, 0xC8] (fun s => s.RIP = 0x110657) (movR64R64Effect 0x110657 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x110657 8 1).toInstrSpec (mov_r64_r64_effect_step 0x110657 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11065a [0x48, 0x81, 0xC1, 0xA0, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x11065a) (addR64Imm32Effect 0x11065a 1 0x9a0)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x11065a 1 0x9a0).toInstrSpec (add_r64_imm32_effect_step 0x11065a 0x48 0xc1 0x9a0 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x110661 [0xBA, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x110661) (movR32Imm32Effect 0x110661 5 2 0x2)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x110661 5 2 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x110661 0xba (by decide) 0x2) pre_rip
  have f3 : InstrSpec 0x110666 [0x31, 0xF6] (fun s => s.RIP = 0x110666) (xorR32R32Effect 0x110666 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x110666 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x110666 0xf6 (by decide)) pre_rip
  have f4 : InstrSpec 0x110668 [0x48, 0xFF, 0xC6] (fun s => s.RIP = 0x110668) (incR64Effect 0x110668 6)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (incR64Effect_footprint 0x110668 6).toInstrSpec (inc_r64_effect_step 0x110668 0x48 0xc6 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11066b [0x4D, 0x85, 0xC0] (fun s => s.RIP = 0x11066b) (testR64R64Effect 0x11066b 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x11066b 8 8).toInstrSpec (test_r64_r64_effect_step 0x11066b 0x4d 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (8, 53), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11065a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (4, 4), (5, 5), (6, 6), (8, 53), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110661) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 57), (4, 4), (5, 5), (6, 6), (8, 53), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110666) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 57), (4, 4), (5, 5), (6, 59), (8, 53), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110668) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 57), (4, 4), (5, 5), (6, 61), (8, 53), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11066b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 57), (4, 4), (5, 5), (6, 61), (8, 53), (11, 11), (12, 12), (13, 13), (14, 14), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11066e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 65) (jcc_rel8_effect_step 0x11066e 5 0xd8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110657 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110657 :=
  Rest.liftedBlock (rest_l110657 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110657 x hx)

theorem rest_l110670 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110670 bytes_l110670) (entryMap (live .l110670))
      1 0x110670 bytes_l110670 b_l110670 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x110670 0xdb (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l110670 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110670 :=
  Rest.liftedBlock (rest_l110670 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110670 x hx)

theorem rest_l110680 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110680 bytes_l110680) (entryMap (live .l110680))
      2 0x110680 bytes_l110680 b_l110680 := by
  have f0 : InstrSpec 0x110680 [0x4C, 0x39, 0xD8] (fun s => s.RIP = 0x110680) (cmpR64R64Effect 0x110680 0 11)
      [.gpr 0, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x110680 0 11).toInstrSpec (cmp_r64_r64_effect_step 0x110680 0x4c 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110683) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x110683 3 0x4b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110680 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110680 :=
  Rest.liftedBlock (rest_l110680 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110680 x hx)

theorem rest_l110685 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110685 bytes_l110685) (entryMap (live .l110685))
      5 0x110685 bytes_l110685 b_l110685 := by
  have f0 : InstrSpec 0x110685 [0x48, 0xFF, 0xC0] (fun s => s.RIP = 0x110685) (incR64Effect 0x110685 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (incR64Effect_footprint 0x110685 0).toInstrSpec (inc_r64_effect_step 0x110685 0x48 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110688 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x110688) (xorR32R32Effect 0x110688 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x110688 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x110688 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11068b [0x4C, 0x8B, 0x5C, 0x24, 0x20] (LoadPre 0x11068b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11068b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11068b 11 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x11068b 11 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x11068b 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x110690 [0x4D, 0x85, 0xC0] (fun s => s.RIP = 0x110690) (testR64R64Effect 0x110690 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x110690 8 8).toInstrSpec (test_r64_r64_effect_step 0x110690 0x4d 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110688) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 55), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11068b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 55), (11, 57), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110690) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 55), (11, 57), (12, 12), (13, 13), (14, 14), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110693) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x110693 5 0xb3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110685 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110685 :=
  Rest.liftedBlock (rest_l110685 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110685 x hx)

theorem rest_l110695 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110695 bytes_l110695) (entryMap (live .l110695))
      1 0x110695 bytes_l110695 b_l110695 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x110695 0xb6 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l110695 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110695 :=
  Rest.liftedBlock (rest_l110695 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110695 x hx)

theorem rest_l1106a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1106a0 bytes_l1106a0) (entryMap (live .l1106a0))
      4 0x1106a0 bytes_l1106a0 b_l1106a0 := by
  have f0 : InstrSpec 0x1106a0 [0x49, 0x89, 0xFA] (fun s => s.RIP = 0x1106a0) (movR64R64Effect 0x1106a0 10 7)
      [.gpr 7] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1106a0 10 7).toInstrSpec (mov_r64_r64_effect_step 0x1106a0 0x49 0xfa (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1106a3 [0x48, 0x81, 0xC7, 0xA0, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x1106a3) (addR64Imm32Effect 0x1106a3 7 0x9a0)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x1106a3 7 0x9a0).toInstrSpec (add_r64_imm32_effect_step 0x1106a3 0x48 0xc7 0x9a0 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1106aa [0x41, 0xB9, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1106aa) (movR32Imm32Effect 0x1106aa 6 9 0x2)
      [] [] [.reg 9, .rip] :=
    (movR32Imm32Effect_footprint 0x1106aa 6 9 0x2).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1106aa 0x41 0xb9 (by decide) (by decide) 0x2) pre_rip
  have f3 : InstrSpec 0x1106b0 [0x45, 0x31, 0xDB] (fun s => s.RIP = 0x1106b0) (xorR32R32Effect 0x1106b0 3 11 11)
      [.gpr 11, .gpr 11] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1106b0 3 11 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x1106b0 0x45 0xdb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (7, 7), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106a3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 4), (5, 5), (7, 55), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106aa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 4), (5, 5), (7, 55), (9, 57), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106b0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (4, 4), (5, 5), (7, 55), (9, 57), (10, 53), (11, 59), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106b3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l1106a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1106a0 :=
  Rest.liftedBlock (rest_l1106a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1106a0 x hx)

theorem rest_l1106b3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1106b3 bytes_l1106b3) (entryMap (live .l1106b3))
      1 0x1106b3 bytes_l1106b3 b_l1106b3 := by
  have f0 : InstrSpec 0x1106b3 [0x49, 0xFF, 0xC3] (fun s => s.RIP = 0x1106b3) (incR64Effect 0x1106b3 11)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (incR64Effect_footprint 0x1106b3 11).toInstrSpec (inc_r64_effect_step 0x1106b3 0x49 0xc3 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106b6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1106b3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1106b3 :=
  Rest.liftedBlock (rest_l1106b3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1106b3 x hx)

theorem rest_l1106b6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1106b6 bytes_l1106b6) (entryMap (live .l1106b6))
      2 0x1106b6 bytes_l1106b6 b_l1106b6 := by
  have f0 : InstrSpec 0x1106b6 [0x4D, 0x85, 0xD2] (fun s => s.RIP = 0x1106b6) (testR64R64Effect 0x1106b6 10 10)
      [.gpr 10, .gpr 10] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1106b6 10 10).toInstrSpec (test_r64_r64_effect_step 0x1106b6 0x4d 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106b9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1106b9 4 0x5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1106b6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1106b6 :=
  Rest.liftedBlock (rest_l1106b6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1106b6 x hx)

theorem rest_l1106bb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1106bb bytes_l1106bb) (entryMap (live .l1106bb))
      2 0x1106bb bytes_l1106bb b_l1106bb := by
  have f0 : InstrSpec 0x1106bb [0x4D, 0x39, 0xCB] (fun s => s.RIP = 0x1106bb) (cmpR64R64Effect 0x1106bb 11 9)
      [.gpr 11, .gpr 9] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1106bb 11 9).toInstrSpec (cmp_r64_r64_effect_step 0x1106bb 0x4d 0xcb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106be) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1106be 2 0xf3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1106bb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1106bb :=
  Rest.liftedBlock (rest_l1106bb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1106bb x hx)

theorem rest_l1106c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1106c0 bytes_l1106c0) (entryMap (live .l1106c0))
      2 0x1106c0 bytes_l1106c0 b_l1106c0 := by
  have f0 : InstrSpec 0x1106c0 [0x48, 0x85, 0xFF] (fun s => s.RIP = 0x1106c0) (testR64R64Effect 0x1106c0 7 7)
      [.gpr 7, .gpr 7] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1106c0 7 7).toInstrSpec (test_r64_r64_effect_step 0x1106c0 0x48 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106c3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1106c3 4 0xb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1106c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1106c0 :=
  Rest.liftedBlock (rest_l1106c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1106c0 x hx)

theorem rest_l1106c5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1106c5 bytes_l1106c5) (entryMap (live .l1106c5))
      2 0x1106c5 bytes_l1106c5 b_l1106c5 := by
  have f0 : InstrSpec 0x1106c5 [0x48, 0x39, 0xEF] (fun s => s.RIP = 0x1106c5) (cmpR64R64Effect 0x1106c5 7 5)
      [.gpr 7, .gpr 5] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1106c5 7 5).toInstrSpec (cmp_r64_r64_effect_step 0x1106c5 0x48 0xef (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106c8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1106c8 5 0xd6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1106c5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1106c5 :=
  Rest.liftedBlock (rest_l1106c5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1106c5 x hx)

theorem rest_l1106ca [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1106ca bytes_l1106ca) (entryMap (live .l1106ca))
      1 0x1106ca bytes_l1106ca b_l1106ca := by
  have f0 : InstrSpec 0x1106ca [0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x1106ca) (fun _ => nopEffect 0x1106ca 6)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1106ca 6).toInstrSpec (nop_m_effect_step 0x1106ca [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106d0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l1106ca [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1106ca :=
  Rest.liftedBlock (rest_l1106ca code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1106ca x hx)

theorem rest_l1106d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1106d0 bytes_l1106d0) (entryMap (live .l1106d0))
      5 0x1106d0 bytes_l1106d0 b_l1106d0 := by
  have f0 : InstrSpec 0x1106d0 [0x4C, 0x8B, 0x04, 0x24] (LoadPre 0x1106d0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1106d0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1106d0 8 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1106d0 8 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1106d0 0x4c (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1106d4 [0x4C, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x1106d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1106d4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1106d4 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1106d4 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1106d4 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1106d9 [0x4C, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x1106d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1106d9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1106d9 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1106d9 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1106d9 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1106de [0x4D, 0x85, 0xC9] (fun s => s.RIP = 0x1106de) (testR64R64Effect 0x1106de 9 9)
      [.gpr 9, .gpr 9] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1106de 9 9).toInstrSpec (test_r64_r64_effect_step 0x1106de 0x4d 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (8, 53), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106d4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 4), (5, 5), (8, 53), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106d9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 4), (5, 5), (8, 53), (9, 55), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106de) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (4, 4), (5, 5), (8, 53), (9, 55), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106e1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel32_effect_step 0x1106e1 5 0xfffffb91) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1106d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1106d0 :=
  Rest.liftedBlock (rest_l1106d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1106d0 x hx)

theorem rest_l1106e7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1106e7 bytes_l1106e7) (entryMap (live .l1106e7))
      1 0x1106e7 bytes_l1106e7 b_l1106e7 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x1106e7 0x71 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1106e7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1106e7 :=
  Rest.liftedBlock (rest_l1106e7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1106e7 x hx)

theorem rest_l1106e9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1106e9 bytes_l1106e9) (entryMap (live .l1106e9))
      14 0x1106e9 bytes_l1106e9 b_l1106e9 := by
  have f0 : InstrSpec 0x1106e9 [0x48, 0x83, 0x3C, 0x24, 0x00] (LoadPre 0x1106e9 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1106e9 + BitVec.ofNat 64 5)) 8) (cmpMImm8Effect 0x1106e9 5 64 (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect64_footprint 0x1106e9 5 (.sib 4 none 0 .none) 0x0).toInstrSpec (cmp_m64_imm8_effect_step 0x1106e9 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1106ee [0x41, 0x0F, 0x94, 0xC3] (fun s => s.RIP = 0x1106ee) (atFlags (condHolds 4) (setccR8Effect 0x1106ee 4 11))
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 11, .rip] :=
    (setccR8Effect_footprint 0x1106ee 4 11 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x1106ee 4 0x41 (by decide) 0xc3 (by decide) c)) pre_rip
  have f2 : InstrSpec 0x1106f2 [0x48, 0x89, 0x54, 0x24, 0x70] (StorePre 0x1106f2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1106f2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1106f2 2 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1106f2 2 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x1106f2 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1106f7 [0x48, 0x89, 0x4C, 0x24, 0x78] (StorePre 0x1106f7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1106f7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1106f7 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1106f7 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x1106f7 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1106fc [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x1106fc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1106fc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1106fc 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1106fc 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1106fc 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x110701 [0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x110701 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x110701 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110701 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110701 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x110701 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x110709 [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x110709 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x110709 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110709 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110709 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x110709 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x110711 [0x48, 0x89, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x110711 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x110711 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110711 6 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110711 6 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x110711 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x110719 [0x48, 0xC7, 0x44, 0x24, 0x68, 0x00, 0x00, 0x00, 0x00] (StorePre 0x110719 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x110719 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x110719 (.sib 4 none 0 (.d8 0x68)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x110719 (.sib 4 none 0 (.d8 0x68)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x110719 0x48 (by decide) (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x110722 [0x4C, 0x89, 0x74, 0x24, 0x58] (StorePre 0x110722 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x110722 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110722 14 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110722 14 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x110722 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x110727 [0x4D, 0x39, 0xD1] (fun s => s.RIP = 0x110727) (cmpR64R64Effect 0x110727 9 10)
      [.gpr 9, .gpr 10] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x110727 9 10).toInstrSpec (cmp_r64_r64_effect_step 0x110727 0x4d 0xd1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11072a [0x0F, 0x93, 0xC0] (fun s => s.RIP = 0x11072a) (atFlags (condHolds 3) (setccR8Effect 0x11072a 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x11072a 3 0 3).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x11072a 3 0xc0 (by decide) (by decide) c)) pre_rip
  have f12 : InstrSpec 0x11072d [0x44, 0x08, 0xD8] (fun s => s.RIP = 0x11072d) (orR8R8Effect 0x11072d 3 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (orR8R8Effect_footprint 0x11072d 3 0 11).toInstrSpec (or_r8_r8_rex_effect_step 0x11072d 0x44 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106ee) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106f2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106f7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1106fc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110701) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110709) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110711) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110719) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110722) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110727) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (16, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11072a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (16, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11072d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f12 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110730) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 72) (jcc_rel8_effect_step 0x110730 5 0x11) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1106e9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1106e9 :=
  Rest.liftedBlock (rest_l1106e9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1106e9 x hx)

theorem rest_l110732 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110732 bytes_l110732) (entryMap (live .l110732))
      3 0x110732 bytes_l110732 b_l110732 := by
  have f0 : InstrSpec 0x110732 [0x49, 0x8D, 0x41, 0x01] (fun s => s.RIP = 0x110732) (leaR64Effect 0x110732 0 (.base 9 (.d8 0x1)))
      [.gpr 9] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x110732 0 (.base 9 (.d8 0x1))).toInstrSpec (lea_r64_effect_step 0x110732 0x49 (by decide) 0 (.base 9 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110736 [0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x110736 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x110736 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110736 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110736 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x110736 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110736) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11073e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 56) (jmp_rel32_effect_step 0x11073e 0xfffffa86 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l110732 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110732 :=
  Rest.liftedBlock (rest_l110732 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110732 x hx)

theorem rest_l110743 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110743 bytes_l110743) (entryMap (live .l110743))
      4 0x110743 bytes_l110743 b_l110743 := by
  have f0 : InstrSpec 0x110743 [0x48, 0x8D, 0xBC, 0x24, 0x30, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x110743) (leaR64Effect 0x110743 7 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x110743 7 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (lea_r64_effect_step 0x110743 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11074b [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11074b) (movR32Imm32Effect 0x11074b 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11074b 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11074b 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x110750 [0x48, 0xC7, 0xC6, 0x48, 0x2D, 0x20, 0x00] (fun s => s.RIP = 0x110750) (movR64Imm32Effect 0x110750 6 0x202d48)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x110750 6 0x202d48).toInstrSpec (mov_r64_imm32_effect_step 0x110750 0x48 0xc6 (by decide) (by decide) (by decide) 0x202d48) pre_rip
  have f3 : InstrSpec 0x110757 [0xF3, 0x48, 0xA5] (RepPre 0x110757 (RepMovsqPre 0x110757)) (repMovsqEffect 0x110757)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x110757).toInstrSpecOfRuns (rep_movsq_runs hstride 0x110757 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11074b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (2, 2), (4, 4), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110750) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (2, 2), (4, 4), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110757) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11075a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l110743 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110743 :=
  Rest.liftedBlock (rest_l110743 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110743 x hx)

theorem rest_l11075a [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11075a bytes_l11075a) (entryMap (live .l11075a))
      13 0x11075a bytes_l11075a b_l11075a := by
  have f0 : InstrSpec 0x11075a [0x48, 0x8D, 0xB4, 0x24, 0x30, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11075a) (leaR64Effect 0x11075a 6 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11075a 6 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (lea_r64_effect_step 0x11075a 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110762 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x110762) (movR32Imm32Effect 0x110762 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x110762 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x110762 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x110767 [0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (LoadPre 0x110767 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x110767 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110767 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x110767 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x110767 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11076f [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x11076f) (movR64R64Effect 0x11076f 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11076f 7 0).toInstrSpec (mov_r64_r64_effect_step 0x11076f 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x110772 [0xF3, 0x48, 0xA5] (RepPre 0x110772 (RepMovsqPre 0x110772)) (repMovsqEffect 0x110772)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x110772).toInstrSpecOfRuns (rep_movsq_runs hstride 0x110772 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x110775 [0x48, 0x81, 0xC4, 0xA8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x110775) (addR64Imm32Effect 0x110775 4 0x1a8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x110775 4 0x1a8).toInstrSpec (add_r64_imm32_effect_step 0x110775 0x48 0xc4 0x1a8 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11077c [0x5B] (PopPre 0x11077c) (popR64Effect 0x11077c 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11077c 1 3).toInstrSpec (pop_r64_effect_step 0x11077c 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x11077d [0x41, 0x5C] (PopPre 0x11077d) (popR64Effect 0x11077d 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11077d 2 12).toInstrSpec (pop_r64_rex_effect_step 0x11077d 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x11077f [0x41, 0x5D] (PopPre 0x11077f) (popR64Effect 0x11077f 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11077f 2 13).toInstrSpec (pop_r64_rex_effect_step 0x11077f 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x110781 [0x41, 0x5E] (PopPre 0x110781) (popR64Effect 0x110781 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110781 2 14).toInstrSpec (pop_r64_rex_effect_step 0x110781 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x110783 [0x41, 0x5F] (PopPre 0x110783) (popR64Effect 0x110783 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110783 2 15).toInstrSpec (pop_r64_rex_effect_step 0x110783 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x110785 [0x5D] (PopPre 0x110785) (popR64Effect 0x110785 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110785 1 5).toInstrSpec (pop_r64_effect_step 0x110785 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f12 : InstrSpec 0x110786 [0xC3] (RetPre 0x110786) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x110786).toInstrSpec (ret_effect_step 0x110786) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110762) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (2, 2), (4, 4), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110767) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (2, 2), (4, 4), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11076f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 55), (2, 2), (4, 4), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110772) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 63) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 63), (2, 2), (4, 4), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110775) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 63), (2, 2), (4, 65), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11077c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 57), (1, 63), (2, 2), (3, 67), (4, 68), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11077d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 57), (1, 63), (2, 2), (3, 67), (4, 71), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11077f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f8 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 57), (1, 63), (2, 2), (3, 67), (4, 74), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110781) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(0, 57), (1, 63), (2, 2), (3, 67), (4, 77), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (14, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110783) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 80) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 81) (ρ' := [(0, 57), (1, 63), (2, 2), (3, 67), (4, 80), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (14, 76), (15, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110785) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f11 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 57), (1, 63), (2, 2), (3, 67), (4, 83), (5, 82), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (14, 76), (15, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110786) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f12 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 87) (ρ' := [(0, 57), (1, 63), (2, 2), (3, 67), (4, 86), (5, 82), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (14, 76), (15, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) f12 (by decide) rfl rfl rfl (by decide)

theorem block_l11075a [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11075a :=
  Rest.liftedBlock (rest_l11075a hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11075a x hx)

theorem rest_l110787 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110787 bytes_l110787) (entryMap (live .l110787))
      3 0x110787 bytes_l110787 b_l110787 := by
  have f0 : InstrSpec 0x110787 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x110787) (movR32Imm32Effect 0x110787 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x110787 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x110787 0xbe (by decide) 0x8) pre_rip
  have f1 : InstrSpec 0x11078c [0x48, 0xC7, 0xC2, 0xD0, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x11078c) (movR64Imm32Effect 0x11078c 2 0x202cd0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x11078c 2 0x202cd0).toInstrSpec (mov_r64_imm32_effect_step 0x11078c 0x48 0xc2 (by decide) (by decide) (by decide) 0x202cd0) pre_rip
  have f2 : InstrSpec 0x110793 [0xE8, 0x5A, 0x8E, 0x01, 0x00] (PushPre 0x110793 5) (callEffect (fun _ => 0x1295f2) 0x110798)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x110793 0x1295f2 0x110798).toInstrSpec (call_rel32_effect_step 0x110793 0x18e5a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 53), (7, 7)]) (p' := 0x11078c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (4, 4), (5, 5), (6, 53), (7, 7)]) (p' := 0x110793) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (4, 57), (5, 5), (6, 53), (7, 7)]) (p' := 0x1295f2) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l110787 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110787 :=
  Rest.liftedBlock (rest_l110787 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110787 x hx)

theorem rest_l110798 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110798 bytes_l110798) (entryMap (live .l110798))
      3 0x110798 bytes_l110798 b_l110798 := by
  have f0 : InstrSpec 0x110798 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x110798) (movR32Imm32Effect 0x110798 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x110798 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x110798 0xbe (by decide) 0x8) pre_rip
  have f1 : InstrSpec 0x11079d [0x48, 0xC7, 0xC2, 0xB8, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x11079d) (movR64Imm32Effect 0x11079d 2 0x202cb8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x11079d 2 0x202cb8).toInstrSpec (mov_r64_imm32_effect_step 0x11079d 0x48 0xc2 (by decide) (by decide) (by decide) 0x202cb8) pre_rip
  have f2 : InstrSpec 0x1107a4 [0xE8, 0x49, 0x8E, 0x01, 0x00] (PushPre 0x1107a4 5) (callEffect (fun _ => 0x1295f2) 0x1107a9)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1107a4 0x1295f2 0x1107a9).toInstrSpec (call_rel32_effect_step 0x1107a4 0x18e49 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 53), (7, 7)]) (p' := 0x11079d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (4, 4), (5, 5), (6, 53), (7, 7)]) (p' := 0x1107a4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (4, 57), (5, 5), (6, 53), (7, 7)]) (p' := 0x1295f2) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l110798 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110798 :=
  Rest.liftedBlock (rest_l110798 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110798 x hx)

theorem rest_l1107a9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1107a9 bytes_l1107a9) (entryMap (live .l1107a9))
      1 0x1107a9 bytes_l1107a9 b_l1107a9 := by
  have f0 : InstrSpec 0x1107a9 [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1107a9) (fun _ => nopEffect 0x1107a9 7)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1107a9 7).toInstrSpec (nop_m_effect_step 0x1107a9 [] (by decide) (by decide) (.base 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107b0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l1107a9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1107a9 :=
  Rest.liftedBlock (rest_l1107a9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1107a9 x hx)

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

theorem_by block_l1100a0_eval :
    program.runBlock (dialect code) ⟨.l1100a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1100c5_eval :
    program.runBlock (dialect code) ⟨.l1100c5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1100db_eval :
    program.runBlock (dialect code) ⟨.l1100db, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1100f1_eval :
    program.runBlock (dialect code) ⟨.l1100f1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110107_eval :
    program.runBlock (dialect code) ⟨.l110107, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110156_eval :
    program.runBlock (dialect code) ⟨.l110156, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11015f_eval :
    program.runBlock (dialect code) ⟨.l11015f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110168_eval :
    program.runBlock (dialect code) ⟨.l110168, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110188_eval :
    program.runBlock (dialect code) ⟨.l110188, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110193_eval :
    program.runBlock (dialect code) ⟨.l110193, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1101c9_eval :
    program.runBlock (dialect code) ⟨.l1101c9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1101de_eval :
    program.runBlock (dialect code) ⟨.l1101de, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110202_eval :
    program.runBlock (dialect code) ⟨.l110202, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110260_eval :
    program.runBlock (dialect code) ⟨.l110260, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110278_eval :
    program.runBlock (dialect code) ⟨.l110278, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110282_eval :
    program.runBlock (dialect code) ⟨.l110282, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1102a0_eval :
    program.runBlock (dialect code) ⟨.l1102a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1102c2_eval :
    program.runBlock (dialect code) ⟨.l1102c2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1102d8_eval :
    program.runBlock (dialect code) ⟨.l1102d8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110300_eval :
    program.runBlock (dialect code) ⟨.l110300, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110305_eval :
    program.runBlock (dialect code) ⟨.l110305, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11031a_eval :
    program.runBlock (dialect code) ⟨.l11031a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110330_eval :
    program.runBlock (dialect code) ⟨.l110330, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11034e_eval :
    program.runBlock (dialect code) ⟨.l11034e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110366_eval :
    program.runBlock (dialect code) ⟨.l110366, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11037b_eval :
    program.runBlock (dialect code) ⟨.l11037b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110380_eval :
    program.runBlock (dialect code) ⟨.l110380, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110385_eval :
    program.runBlock (dialect code) ⟨.l110385, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11038a_eval :
    program.runBlock (dialect code) ⟨.l11038a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11038f_eval :
    program.runBlock (dialect code) ⟨.l11038f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110398_eval :
    program.runBlock (dialect code) ⟨.l110398, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1103a1_eval :
    program.runBlock (dialect code) ⟨.l1103a1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1103c0_eval :
    program.runBlock (dialect code) ⟨.l1103c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1103c7_eval :
    program.runBlock (dialect code) ⟨.l1103c7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1103d1_eval :
    program.runBlock (dialect code) ⟨.l1103d1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110400_eval :
    program.runBlock (dialect code) ⟨.l110400, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110418_eval :
    program.runBlock (dialect code) ⟨.l110418, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110600_eval :
    program.runBlock (dialect code) ⟨.l110600, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11062b_eval :
    program.runBlock (dialect code) ⟨.l11062b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11063a_eval :
    program.runBlock (dialect code) ⟨.l11063a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110640_eval :
    program.runBlock (dialect code) ⟨.l110640, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110648_eval :
    program.runBlock (dialect code) ⟨.l110648, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11064d_eval :
    program.runBlock (dialect code) ⟨.l11064d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110652_eval :
    program.runBlock (dialect code) ⟨.l110652, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110657_eval :
    program.runBlock (dialect code) ⟨.l110657, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110670_eval :
    program.runBlock (dialect code) ⟨.l110670, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110680_eval :
    program.runBlock (dialect code) ⟨.l110680, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110685_eval :
    program.runBlock (dialect code) ⟨.l110685, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110695_eval :
    program.runBlock (dialect code) ⟨.l110695, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1106a0_eval :
    program.runBlock (dialect code) ⟨.l1106a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1106b3_eval :
    program.runBlock (dialect code) ⟨.l1106b3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1106b6_eval :
    program.runBlock (dialect code) ⟨.l1106b6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1106bb_eval :
    program.runBlock (dialect code) ⟨.l1106bb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1106c0_eval :
    program.runBlock (dialect code) ⟨.l1106c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1106c5_eval :
    program.runBlock (dialect code) ⟨.l1106c5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1106ca_eval :
    program.runBlock (dialect code) ⟨.l1106ca, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1106d0_eval :
    program.runBlock (dialect code) ⟨.l1106d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1106e7_eval :
    program.runBlock (dialect code) ⟨.l1106e7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1106e9_eval :
    program.runBlock (dialect code) ⟨.l1106e9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110732_eval :
    program.runBlock (dialect code) ⟨.l110732, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110743_eval :
    program.runBlock (dialect code) ⟨.l110743, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11075a_eval :
    program.runBlock (dialect code) ⟨.l11075a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110787_eval :
    program.runBlock (dialect code) ⟨.l110787, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110798_eval :
    program.runBlock (dialect code) ⟨.l110798, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1107a9_eval :
    program.runBlock (dialect code) ⟨.l1107a9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
