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

theorem rest_l128e40 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128e40 bytes_l128e40) (entryMap (live .l128e40))
      16 0x128e40 bytes_l128e40 b_l128e40 := by
  have f0 : InstrSpec 0x128e40 [0x55] (PushPre 0x128e40 1) (pushR64Effect 0x128e40 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128e40 1 5).toInstrSpec (push_r64_effect_step 0x128e40 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x128e41 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x128e41) (movR64R64Effect 0x128e41 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x128e41 5 4).toInstrSpec (mov_r64_r64_effect_step 0x128e41 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128e44 [0x41, 0x57] (PushPre 0x128e44 2) (pushR64Effect 0x128e44 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128e44 2 15).toInstrSpec (push_r64_rex_effect_step 0x128e44 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x128e46 [0x41, 0x56] (PushPre 0x128e46 2) (pushR64Effect 0x128e46 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128e46 2 14).toInstrSpec (push_r64_rex_effect_step 0x128e46 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x128e48 [0x41, 0x55] (PushPre 0x128e48 2) (pushR64Effect 0x128e48 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128e48 2 13).toInstrSpec (push_r64_rex_effect_step 0x128e48 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x128e4a [0x41, 0x54] (PushPre 0x128e4a 2) (pushR64Effect 0x128e4a 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128e4a 2 12).toInstrSpec (push_r64_rex_effect_step 0x128e4a 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x128e4c [0x53] (PushPre 0x128e4c 1) (pushR64Effect 0x128e4c 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128e4c 1 3).toInstrSpec (push_r64_effect_step 0x128e4c 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x128e4d [0x48, 0x83, 0xEC, 0x48] (fun s => s.RIP = 0x128e4d) (subR64Imm8Effect 0x128e4d 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x128e4d 4 0x48).toInstrSpec (sub_r64_imm8_effect_step 0x128e4d 0x48 0xec 0x48 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x128e51 [0x4C, 0x89, 0x45, 0xC0] (StorePre 0x128e51 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x128e51 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128e51 8 (.base 5 (.d8 0xc0)))
      [.gpr 8, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x128e51 8 (.base 5 (.d8 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x128e51 0x4c (by decide) 0 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x128e55 [0x48, 0x89, 0x4D, 0xC8] (StorePre 0x128e55 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x128e55 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128e55 1 (.base 5 (.d8 0xc8)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x128e55 1 (.base 5 (.d8 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x128e55 0x48 (by decide) 1 (.base 5 (.d8 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x128e59 [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x128e59) (movR64R64Effect 0x128e59 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x128e59 15 2).toInstrSpec (mov_r64_r64_effect_step 0x128e59 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x128e5c [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x128e5c) (movR64R64Effect 0x128e5c 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x128e5c 14 7).toInstrSpec (mov_r64_r64_effect_step 0x128e5c 0x49 0xfe (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x128e5f [0x4C, 0x8B, 0x27] (LoadPre 0x128e5f (fun s => AddrMode.addr (.base 7 .none) s (0x128e5f + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128e5f 12 (.base 7 .none))
      [.gpr 7] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x128e5f 12 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128e5f 0x4c (by decide) 4 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x128e62 [0x48, 0x8B, 0x5F, 0x08] (LoadPre 0x128e62 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x128e62 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128e62 3 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x128e62 3 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x128e62 0x48 (by decide) 3 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x128e66 [0x4C, 0x8B, 0x6B, 0x18] (LoadPre 0x128e66 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x128e66 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128e66 13 (.base 3 (.d8 0x18)))
      [.gpr 3] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x128e66 13 (.base 3 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x128e66 0x4c (by decide) 5 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x128e6a [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x128e6a) (movR64R64Effect 0x128e6a 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128e6a 7 12).toInstrSpec (mov_r64_r64_effect_step 0x128e6a 0x4c 0xe7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x128e41) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 55), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x128e44) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 55), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x128e46) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 55), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x128e48) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 55), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x128e4a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 55), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x128e4c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 55), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x128e4d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(1, 1), (2, 2), (3, 3), (5, 55), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x128e51) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (5, 55), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x128e55) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(1, 1), (2, 2), (3, 3), (5, 55), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x128e59) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 3), (5, 55), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14)]) (p' := 0x128e5c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(1, 1), (2, 2), (3, 3), (5, 55), (7, 7), (8, 8), (12, 12), (13, 13)]) (p' := 0x128e5f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(1, 1), (2, 2), (3, 3), (5, 55), (7, 7), (8, 8), (12, 72), (13, 13)]) (p' := 0x128e62) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(1, 1), (2, 2), (3, 74), (5, 55), (7, 7), (8, 8), (12, 72), (13, 13)]) (p' := 0x128e66) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 2), (3, 74), (5, 55), (7, 7), (8, 8), (12, 72)]) (p' := 0x128e6a) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(1, 1), (2, 2), (3, 74), (5, 55), (8, 8), (12, 72)]) (p' := 0x128e6d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128e40 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128e40 :=
  Rest.liftedBlock (rest_l128e40 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128e40 x hx)

theorem rest_l128e70 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128e70 bytes_l128e70) (entryMap (live .l128e70))
      3 0x128e70 bytes_l128e70 b_l128e70 := by
  have f0 : InstrSpec 0x128e70 [0xB1, 0x01] (fun s => s.RIP = 0x128e70) (movR8Imm8Effect 0x128e70 2 1 0x1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x128e70 2 1 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x128e70 0xb1 (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x128e72 [0x84, 0xC0] (fun s => s.RIP = 0x128e72) (testR8R8Effect 0x128e72 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128e72 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x128e72 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128e72) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128e74) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x128e74 5 0xad) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128e70 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128e70 :=
  Rest.liftedBlock (rest_l128e70 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128e70 x hx)

theorem rest_l128e7a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128e7a bytes_l128e7a) (entryMap (live .l128e7a))
      2 0x128e7a bytes_l128e7a b_l128e7a := by
  have f0 : InstrSpec 0x128e7a [0x41, 0xF6, 0x46, 0x12, 0x80] (LoadPre 0x128e7a (fun s => AddrMode.addr (.base 14 (.d8 0x12)) s (0x128e7a + BitVec.ofNat 64 5)) 1) (testM8Imm8Effect 0x128e7a 5 (.base 14 (.d8 0x12)) 0x80)
      [.gpr 14] [] [.flags, .rip] :=
    (testM8Imm8Effect_footprint 0x128e7a 5 (.base 14 (.d8 0x12)) 0x80).toInstrSpec (test_m8_imm8_rex_effect_step 0x128e7a 0x41 (by decide) (.base 14 (.d8 0x12)) (by decide) (by decide) (by decide) 0x80) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(12, 12), (14, 14), (19, 53)]) (p' := 0x128e7f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128e7f 5 0x31) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128e7a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128e7a :=
  Rest.liftedBlock (rest_l128e7a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128e7a x hx)

theorem rest_l128e81 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128e81 bytes_l128e81) (entryMap (live .l128e81))
      3 0x128e81 bytes_l128e81 b_l128e81 := by
  have f0 : InstrSpec 0x128e81 [0x48, 0x8D, 0x35, 0xA8, 0xAD, 0x0D, 0x00] (fun s => s.RIP = 0x128e81) (leaR64Effect 0x128e81 6 (.rip 0xdada8))
      [] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x128e81 6 (.rip 0xdada8)).toInstrSpec (lea_r64_effect_step 0x128e81 0x48 (by decide) 6 (.rip 0xdada8) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128e88 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128e88) (movR32Imm32Effect 0x128e88 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x128e88 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x128e88 0xba (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x128e8d [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x128e8d) (movR64R64Effect 0x128e8d 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128e8d 7 12).toInstrSpec (mov_r64_r64_effect_step 0x128e8d 0x4c 0xe7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(12, 12)]) (p' := 0x128e88) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(12, 12)]) (p' := 0x128e8d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(12, 12)]) (p' := 0x128e90) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128e81 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128e81 :=
  Rest.liftedBlock (rest_l128e81 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128e81 x hx)

theorem rest_l128e93 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128e93 bytes_l128e93) (entryMap (live .l128e93))
      2 0x128e93 bytes_l128e93 b_l128e93 := by
  have f0 : InstrSpec 0x128e93 [0x84, 0xC0] (fun s => s.RIP = 0x128e93) (testR8R8Effect 0x128e93 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128e93 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x128e93 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128e95) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x128e95 5 0x8a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128e93 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128e93 :=
  Rest.liftedBlock (rest_l128e93 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128e93 x hx)

theorem rest_l128e9b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128e9b bytes_l128e9b) (entryMap (live .l128e9b))
      3 0x128e9b bytes_l128e9b b_l128e9b := by
  have f0 : InstrSpec 0x128e9b [0x48, 0x8B, 0x7D, 0xC8] (LoadPre 0x128e9b (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x128e9b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128e9b 7 (.base 5 (.d8 0xc8)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x128e9b 7 (.base 5 (.d8 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x128e9b 0x48 (by decide) 7 (.base 5 (.d8 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128e9f [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x128e9f) (movR64R64Effect 0x128e9f 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x128e9f 6 14).toInstrSpec (mov_r64_r64_effect_step 0x128e9f 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128ea2 [0x48, 0x8B, 0x45, 0xC0] (LoadPre 0x128ea2 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x128ea2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128ea2 0 (.base 5 (.d8 0xc0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128ea2 0 (.base 5 (.d8 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x128ea2 0x48 (by decide) 0 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(5, 5), (14, 14)]) (p' := 0x128e9f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(5, 5), (14, 14)]) (p' := 0x128ea2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(5, 5), (14, 14)]) (p' := 0x128ea6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128e9b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128e9b :=
  Rest.liftedBlock (rest_l128e9b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128e9b x hx)

theorem rest_l128ea9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128ea9 bytes_l128ea9) (entryMap (live .l128ea9))
      2 0x128ea9 bytes_l128ea9 b_l128ea9 := by
  have f0 : InstrSpec 0x128ea9 [0x84, 0xC0] (fun s => s.RIP = 0x128ea9) (testR8R8Effect 0x128ea9 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128ea9 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x128ea9 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128eab) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128eab 5 0x78) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128ea9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128ea9 :=
  Rest.liftedBlock (rest_l128ea9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128ea9 x hx)

theorem rest_l128ead [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128ead bytes_l128ead) (entryMap (live .l128ead))
      1 0x128ead bytes_l128ead b_l128ead := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x128ead 0x86 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l128ead [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128ead :=
  Rest.liftedBlock (rest_l128ead code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128ead x hx)

theorem rest_l128eb2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128eb2 bytes_l128eb2) (entryMap (live .l128eb2))
      3 0x128eb2 bytes_l128eb2 b_l128eb2 := by
  have f0 : InstrSpec 0x128eb2 [0x48, 0x8D, 0x35, 0x78, 0xAD, 0x0D, 0x00] (fun s => s.RIP = 0x128eb2) (leaR64Effect 0x128eb2 6 (.rip 0xdad78))
      [] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x128eb2 6 (.rip 0xdad78)).toInstrSpec (lea_r64_effect_step 0x128eb2 0x48 (by decide) 6 (.rip 0xdad78) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128eb9 [0xBA, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128eb9) (movR32Imm32Effect 0x128eb9 5 2 0x2)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x128eb9 5 2 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x128eb9 0xba (by decide) 0x2) pre_rip
  have f2 : InstrSpec 0x128ebe [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x128ebe) (movR64R64Effect 0x128ebe 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128ebe 7 12).toInstrSpec (mov_r64_r64_effect_step 0x128ebe 0x4c 0xe7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(12, 12)]) (p' := 0x128eb9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(12, 12)]) (p' := 0x128ebe) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(12, 12)]) (p' := 0x128ec1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128eb2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128eb2 :=
  Rest.liftedBlock (rest_l128eb2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128eb2 x hx)

theorem rest_l128ec4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128ec4 bytes_l128ec4) (entryMap (live .l128ec4))
      2 0x128ec4 bytes_l128ec4 b_l128ec4 := by
  have f0 : InstrSpec 0x128ec4 [0x84, 0xC0] (fun s => s.RIP = 0x128ec4) (testR8R8Effect 0x128ec4 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128ec4 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x128ec4 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ec6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128ec6 5 0x5d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128ec4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128ec4 :=
  Rest.liftedBlock (rest_l128ec4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128ec4 x hx)

theorem rest_l128ec8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128ec8 bytes_l128ec8) (entryMap (live .l128ec8))
      14 0x128ec8 bytes_l128ec8 b_l128ec8 := by
  have f0 : InstrSpec 0x128ec8 [0xC6, 0x45, 0xD7, 0x01] (StorePre 0x128ec8 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd7)) s (0x128ec8 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x128ec8 (.base 5 (.d8 0xd7)) 0x1)
      [.gpr 5] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x128ec8 (.base 5 (.d8 0xd7)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x128ec8 (.base 5 (.d8 0xd7)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x128ecc [0x4C, 0x89, 0x65, 0x90] (StorePre 0x128ecc 4 (fun s => AddrMode.addr (.base 5 (.d8 0x90)) s (0x128ecc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128ecc 12 (.base 5 (.d8 0x90)))
      [.gpr 12, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x128ecc 12 (.base 5 (.d8 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x128ecc 0x4c (by decide) 4 (.base 5 (.d8 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x128ed0 [0x48, 0x89, 0x5D, 0x98] (StorePre 0x128ed0 4 (fun s => AddrMode.addr (.base 5 (.d8 0x98)) s (0x128ed0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128ed0 3 (.base 5 (.d8 0x98)))
      [.gpr 3, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x128ed0 3 (.base 5 (.d8 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x128ed0 0x48 (by decide) 3 (.base 5 (.d8 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x128ed4 [0x48, 0x8D, 0x45, 0xD7] (fun s => s.RIP = 0x128ed4) (leaR64Effect 0x128ed4 0 (.base 5 (.d8 0xd7)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x128ed4 0 (.base 5 (.d8 0xd7))).toInstrSpec (lea_r64_effect_step 0x128ed4 0x48 (by decide) 0 (.base 5 (.d8 0xd7)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x128ed8 [0x48, 0x89, 0x45, 0xA0] (StorePre 0x128ed8 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa0)) s (0x128ed8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128ed8 0 (.base 5 (.d8 0xa0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x128ed8 0 (.base 5 (.d8 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x128ed8 0x48 (by decide) 0 (.base 5 (.d8 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x128edc [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x128edc (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x128edc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128edc 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128edc 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x128edc 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x128ee0 [0x48, 0x89, 0x45, 0xB8] (StorePre 0x128ee0 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x128ee0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128ee0 0 (.base 5 (.d8 0xb8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x128ee0 0 (.base 5 (.d8 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x128ee0 0x48 (by decide) 0 (.base 5 (.d8 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x128ee4 [0x48, 0x8D, 0x45, 0x90] (fun s => s.RIP = 0x128ee4) (leaR64Effect 0x128ee4 0 (.base 5 (.d8 0x90)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x128ee4 0 (.base 5 (.d8 0x90))).toInstrSpec (lea_r64_effect_step 0x128ee4 0x48 (by decide) 0 (.base 5 (.d8 0x90)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x128ee8 [0x48, 0x89, 0x45, 0xA8] (StorePre 0x128ee8 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x128ee8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128ee8 0 (.base 5 (.d8 0xa8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x128ee8 0 (.base 5 (.d8 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x128ee8 0x48 (by decide) 0 (.base 5 (.d8 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x128eec [0x48, 0x8D, 0x05, 0x95, 0xAE, 0x0D, 0x00] (fun s => s.RIP = 0x128eec) (leaR64Effect 0x128eec 0 (.rip 0xdae95))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x128eec 0 (.rip 0xdae95)).toInstrSpec (lea_r64_effect_step 0x128eec 0x48 (by decide) 0 (.rip 0xdae95) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x128ef3 [0x48, 0x89, 0x45, 0xB0] (StorePre 0x128ef3 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb0)) s (0x128ef3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128ef3 0 (.base 5 (.d8 0xb0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x128ef3 0 (.base 5 (.d8 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x128ef3 0x48 (by decide) 0 (.base 5 (.d8 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x128ef7 [0x48, 0x8D, 0x75, 0xA8] (fun s => s.RIP = 0x128ef7) (leaR64Effect 0x128ef7 6 (.base 5 (.d8 0xa8)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x128ef7 6 (.base 5 (.d8 0xa8))).toInstrSpec (lea_r64_effect_step 0x128ef7 0x48 (by decide) 6 (.base 5 (.d8 0xa8)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x128efb [0x48, 0x8B, 0x7D, 0xC8] (LoadPre 0x128efb (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x128efb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128efb 7 (.base 5 (.d8 0xc8)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x128efb 7 (.base 5 (.d8 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x128efb 0x48 (by decide) 7 (.base 5 (.d8 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x128eff [0x48, 0x8B, 0x45, 0xC0] (LoadPre 0x128eff (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x128eff + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128eff 0 (.base 5 (.d8 0xc0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128eff 0 (.base 5 (.d8 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x128eff 0x48 (by decide) 0 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (5, 5), (12, 12), (14, 14)]) (p' := 0x128ecc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (5, 5), (12, 12), (14, 14)]) (p' := 0x128ed0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (5, 5), (12, 12), (14, 14)]) (p' := 0x128ed4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (5, 5), (12, 12), (14, 14)]) (p' := 0x128ed8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (5, 5), (12, 12), (14, 14)]) (p' := 0x128edc) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (5, 5), (12, 12), (14, 14)]) (p' := 0x128ee0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (5, 5), (12, 12), (14, 14)]) (p' := 0x128ee4) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (5, 5), (12, 12), (14, 14)]) (p' := 0x128ee8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (5, 5), (12, 12), (14, 14)]) (p' := 0x128eec) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (5, 5), (12, 12), (14, 14)]) (p' := 0x128ef3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (5, 5), (12, 12), (14, 14)]) (p' := 0x128ef7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 65), (3, 3), (5, 5), (12, 12), (14, 14)]) (p' := 0x128efb) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 65), (3, 3), (5, 5), (12, 12), (14, 14)]) (p' := 0x128eff) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(3, 3), (5, 5), (12, 12), (14, 14)]) (p' := 0x128f03) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128ec8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128ec8 :=
  Rest.liftedBlock (rest_l128ec8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128ec8 x hx)

theorem rest_l128f06 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128f06 bytes_l128f06) (entryMap (live .l128f06))
      2 0x128f06 bytes_l128f06 b_l128f06 := by
  have f0 : InstrSpec 0x128f06 [0x84, 0xC0] (fun s => s.RIP = 0x128f06) (testR8R8Effect 0x128f06 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128f06 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x128f06 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128f08) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128f08 5 0x1b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128f06 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128f06 :=
  Rest.liftedBlock (rest_l128f06 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128f06 x hx)

theorem rest_l128f0a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128f0a bytes_l128f0a) (entryMap (live .l128f0a))
      4 0x128f0a bytes_l128f0a b_l128f0a := by
  have f0 : InstrSpec 0x128f0a [0x48, 0x8B, 0x7D, 0xA8] (LoadPre 0x128f0a (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x128f0a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128f0a 7 (.base 5 (.d8 0xa8)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x128f0a 7 (.base 5 (.d8 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x128f0a 0x48 (by decide) 7 (.base 5 (.d8 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128f0e [0x48, 0x8B, 0x45, 0xB0] (LoadPre 0x128f0e (fun s => AddrMode.addr (.base 5 (.d8 0xb0)) s (0x128f0e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128f0e 0 (.base 5 (.d8 0xb0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128f0e 0 (.base 5 (.d8 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x128f0e 0x48 (by decide) 0 (.base 5 (.d8 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128f12 [0x48, 0x8D, 0x35, 0x15, 0xAD, 0x0D, 0x00] (fun s => s.RIP = 0x128f12) (leaR64Effect 0x128f12 6 (.rip 0xdad15))
      [] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x128f12 6 (.rip 0xdad15)).toInstrSpec (lea_r64_effect_step 0x128f12 0x48 (by decide) 6 (.rip 0xdad15) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x128f19 [0xBA, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128f19) (movR32Imm32Effect 0x128f19 5 2 0x2)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x128f19 5 2 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x128f19 0xba (by decide) 0x2) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(5, 5)]) (p' := 0x128f0e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(5, 5)]) (p' := 0x128f12) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(5, 5)]) (p' := 0x128f19) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(5, 5)]) (p' := 0x128f1e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128f0a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128f0a :=
  Rest.liftedBlock (rest_l128f0a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128f0a x hx)

theorem rest_l128f21 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128f21 bytes_l128f21) (entryMap (live .l128f21))
      2 0x128f21 bytes_l128f21 b_l128f21 := by
  have f0 : InstrSpec 0x128f21 [0x84, 0xC0] (fun s => s.RIP = 0x128f21) (testR8R8Effect 0x128f21 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128f21 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x128f21 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128f23) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128f23 4 0x13) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128f21 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128f21 :=
  Rest.liftedBlock (rest_l128f21 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128f21 x hx)

theorem rest_l128f25 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128f25 bytes_l128f25) (entryMap (live .l128f25))
      1 0x128f25 bytes_l128f25 b_l128f25 := by
  have f0 : InstrSpec 0x128f25 [0xB1, 0x01] (fun s => s.RIP = 0x128f25) (movR8Imm8Effect 0x128f25 2 1 0x1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x128f25 2 1 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x128f25 0xb1 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128f27) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l128f25 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128f25 :=
  Rest.liftedBlock (rest_l128f25 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128f25 x hx)

theorem rest_l128f27 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128f27 bytes_l128f27) (entryMap (live .l128f27))
      9 0x128f27 bytes_l128f27 b_l128f27 := by
  have f0 : InstrSpec 0x128f27 [0x89, 0xC8] (fun s => s.RIP = 0x128f27) (movR32R32Effect 0x128f27 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x128f27 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x128f27 0xc8 (by decide)) pre_rip
  have f1 : InstrSpec 0x128f29 [0x48, 0x83, 0xC4, 0x48] (fun s => s.RIP = 0x128f29) (addR64Imm8Effect 0x128f29 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x128f29 4 0x48).toInstrSpec (add_r64_imm8_effect_step 0x128f29 0x48 0xc4 0x48 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128f2d [0x5B] (PopPre 0x128f2d) (popR64Effect 0x128f2d 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128f2d 1 3).toInstrSpec (pop_r64_effect_step 0x128f2d 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x128f2e [0x41, 0x5C] (PopPre 0x128f2e) (popR64Effect 0x128f2e 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128f2e 2 12).toInstrSpec (pop_r64_rex_effect_step 0x128f2e 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x128f30 [0x41, 0x5D] (PopPre 0x128f30) (popR64Effect 0x128f30 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128f30 2 13).toInstrSpec (pop_r64_rex_effect_step 0x128f30 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x128f32 [0x41, 0x5E] (PopPre 0x128f32) (popR64Effect 0x128f32 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128f32 2 14).toInstrSpec (pop_r64_rex_effect_step 0x128f32 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x128f34 [0x41, 0x5F] (PopPre 0x128f34) (popR64Effect 0x128f34 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128f34 2 15).toInstrSpec (pop_r64_rex_effect_step 0x128f34 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x128f36 [0x5D] (PopPre 0x128f36) (popR64Effect 0x128f36 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128f36 1 5).toInstrSpec (pop_r64_effect_step 0x128f36 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x128f37 [0xC3] (RetPre 0x128f37) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x128f37).toInstrSpec (ret_effect_step 0x128f37) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128f29) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128f2d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128f2e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128f30) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128f32) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128f34) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128f36) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128f37) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l128f27 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128f27 :=
  Rest.liftedBlock (rest_l128f27 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128f27 x hx)

theorem rest_l128f38 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128f38 bytes_l128f38) (entryMap (live .l128f38))
      2 0x128f38 bytes_l128f38 b_l128f38 := by
  have f0 : InstrSpec 0x128f38 [0x4D, 0x85, 0xFF] (fun s => s.RIP = 0x128f38) (testR64R64Effect 0x128f38 15 15)
      [.gpr 15, .gpr 15] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x128f38 15 15).toInstrSpec (test_r64_r64_effect_step 0x128f38 0x4d 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(14, 14), (15, 15), (19, 53)]) (p' := 0x128f3b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128f3b 5 0x23) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128f38 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128f38 :=
  Rest.liftedBlock (rest_l128f38 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128f38 x hx)

theorem rest_l128f3d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128f3d bytes_l128f3d) (entryMap (live .l128f3d))
      2 0x128f3d bytes_l128f3d b_l128f3d := by
  have f0 : InstrSpec 0x128f3d [0x41, 0xF6, 0x46, 0x12, 0x80] (LoadPre 0x128f3d (fun s => AddrMode.addr (.base 14 (.d8 0x12)) s (0x128f3d + BitVec.ofNat 64 5)) 1) (testM8Imm8Effect 0x128f3d 5 (.base 14 (.d8 0x12)) 0x80)
      [.gpr 14] [] [.flags, .rip] :=
    (testM8Imm8Effect_footprint 0x128f3d 5 (.base 14 (.d8 0x12)) 0x80).toInstrSpec (test_m8_imm8_rex_effect_step 0x128f3d 0x41 (by decide) (.base 14 (.d8 0x12)) (by decide) (by decide) (by decide) 0x80) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(14, 14), (19, 53)]) (p' := 0x128f42) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128f42 5 0x1c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128f3d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128f3d :=
  Rest.liftedBlock (rest_l128f3d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128f3d x hx)

theorem rest_l128f44 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128f44 bytes_l128f44) (entryMap (live .l128f44))
      4 0x128f44 bytes_l128f44 b_l128f44 := by
  have f0 : InstrSpec 0x128f44 [0x49, 0x8B, 0x3E] (LoadPre 0x128f44 (fun s => AddrMode.addr (.base 14 .none) s (0x128f44 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128f44 7 (.base 14 .none))
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x128f44 7 (.base 14 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128f44 0x49 (by decide) 7 (.base 14 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128f47 [0x49, 0x8B, 0x46, 0x08] (LoadPre 0x128f47 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x128f47 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128f47 0 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128f47 0 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x128f47 0x49 (by decide) 0 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128f4b [0x48, 0x8D, 0x35, 0xE3, 0xAC, 0x0D, 0x00] (fun s => s.RIP = 0x128f4b) (leaR64Effect 0x128f4b 6 (.rip 0xdace3))
      [] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x128f4b 6 (.rip 0xdace3)).toInstrSpec (lea_r64_effect_step 0x128f4b 0x48 (by decide) 6 (.rip 0xdace3) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x128f52 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128f52) (movR32Imm32Effect 0x128f52 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x128f52 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x128f52 0xba (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(14, 14)]) (p' := 0x128f47) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(14, 14)]) (p' := 0x128f4b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(14, 14)]) (p' := 0x128f52) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(14, 14)]) (p' := 0x128f57) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128f44 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128f44 :=
  Rest.liftedBlock (rest_l128f44 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128f44 x hx)

theorem rest_l128f5a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128f5a bytes_l128f5a) (entryMap (live .l128f5a))
      3 0x128f5a bytes_l128f5a b_l128f5a := by
  have f0 : InstrSpec 0x128f5a [0xB1, 0x01] (fun s => s.RIP = 0x128f5a) (movR8Imm8Effect 0x128f5a 2 1 0x1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x128f5a 2 1 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x128f5a 0xb1 (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x128f5c [0x84, 0xC0] (fun s => s.RIP = 0x128f5c) (testR8R8Effect 0x128f5c 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128f5c 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x128f5c 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128f5c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128f5e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x128f5e 5 0xc7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128f5a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128f5a :=
  Rest.liftedBlock (rest_l128f5a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128f5a x hx)

theorem rest_l128f60 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128f60 bytes_l128f60) (entryMap (live .l128f60))
      4 0x128f60 bytes_l128f60 b_l128f60 := by
  have f0 : InstrSpec 0x128f60 [0x49, 0x8B, 0x3E] (LoadPre 0x128f60 (fun s => AddrMode.addr (.base 14 .none) s (0x128f60 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128f60 7 (.base 14 .none))
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x128f60 7 (.base 14 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128f60 0x49 (by decide) 7 (.base 14 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128f63 [0x49, 0x8B, 0x46, 0x08] (LoadPre 0x128f63 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x128f63 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128f63 0 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128f63 0 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x128f63 0x49 (by decide) 0 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128f67 [0x48, 0x8D, 0x35, 0xC6, 0xAC, 0x0D, 0x00] (fun s => s.RIP = 0x128f67) (leaR64Effect 0x128f67 6 (.rip 0xdacc6))
      [] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x128f67 6 (.rip 0xdacc6)).toInstrSpec (lea_r64_effect_step 0x128f67 0x48 (by decide) 6 (.rip 0xdacc6) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x128f6e [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128f6e) (movR32Imm32Effect 0x128f6e 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x128f6e 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x128f6e 0xba (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(14, 14)]) (p' := 0x128f63) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(14, 14)]) (p' := 0x128f67) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(14, 14)]) (p' := 0x128f6e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(14, 14)]) (p' := 0x128f73) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128f60 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128f60 :=
  Rest.liftedBlock (rest_l128f60 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128f60 x hx)

theorem rest_l128f76 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128f76 bytes_l128f76) (entryMap (live .l128f76))
      2 0x128f76 bytes_l128f76 b_l128f76 := by
  have f0 : InstrSpec 0x128f76 [0x89, 0xC1] (fun s => s.RIP = 0x128f76) (movR32R32Effect 0x128f76 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x128f76 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x128f76 0xc1 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128f78) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x128f78 0xad (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l128f76 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128f76 :=
  Rest.liftedBlock (rest_l128f76 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128f76 x hx)

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

theorem_by block_l128e40_eval :
    program.runBlock (dialect code) ⟨.l128e40, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128e70_eval :
    program.runBlock (dialect code) ⟨.l128e70, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128e7a_eval :
    program.runBlock (dialect code) ⟨.l128e7a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128e81_eval :
    program.runBlock (dialect code) ⟨.l128e81, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128e93_eval :
    program.runBlock (dialect code) ⟨.l128e93, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128e9b_eval :
    program.runBlock (dialect code) ⟨.l128e9b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128ea9_eval :
    program.runBlock (dialect code) ⟨.l128ea9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128ead_eval :
    program.runBlock (dialect code) ⟨.l128ead, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128eb2_eval :
    program.runBlock (dialect code) ⟨.l128eb2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128ec4_eval :
    program.runBlock (dialect code) ⟨.l128ec4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128ec8_eval :
    program.runBlock (dialect code) ⟨.l128ec8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128f06_eval :
    program.runBlock (dialect code) ⟨.l128f06, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128f0a_eval :
    program.runBlock (dialect code) ⟨.l128f0a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128f21_eval :
    program.runBlock (dialect code) ⟨.l128f21, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128f25_eval :
    program.runBlock (dialect code) ⟨.l128f25, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128f27_eval :
    program.runBlock (dialect code) ⟨.l128f27, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128f38_eval :
    program.runBlock (dialect code) ⟨.l128f38, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128f3d_eval :
    program.runBlock (dialect code) ⟨.l128f3d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128f44_eval :
    program.runBlock (dialect code) ⟨.l128f44, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128f5a_eval :
    program.runBlock (dialect code) ⟨.l128f5a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128f60_eval :
    program.runBlock (dialect code) ⟨.l128f60, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128f76_eval :
    program.runBlock (dialect code) ⟨.l128f76, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
