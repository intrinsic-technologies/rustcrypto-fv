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

theorem rest_l102630 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102630 bytes_l102630) (entryMap (live .l102630))
      10 0x102630 bytes_l102630 b_l102630 := by
  have f0 : InstrSpec 0x102630 [0x41, 0x57] (PushPre 0x102630 2) (pushR64Effect 0x102630 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102630 2 15).toInstrSpec (push_r64_rex_effect_step 0x102630 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x102632 [0x41, 0x56] (PushPre 0x102632 2) (pushR64Effect 0x102632 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102632 2 14).toInstrSpec (push_r64_rex_effect_step 0x102632 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x102634 [0x41, 0x54] (PushPre 0x102634 2) (pushR64Effect 0x102634 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102634 2 12).toInstrSpec (push_r64_rex_effect_step 0x102634 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x102636 [0x53] (PushPre 0x102636 1) (pushR64Effect 0x102636 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102636 1 3).toInstrSpec (push_r64_effect_step 0x102636 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x102637 [0x48, 0x81, 0xEC, 0xB8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102637) (subR64Imm32Effect 0x102637 4 0x1b8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x102637 4 0x1b8).toInstrSpec (sub_r64_imm32_effect_step 0x102637 0x48 0xec 0x1b8 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10263e [0x49, 0x89, 0xCE] (fun s => s.RIP = 0x10263e) (movR64R64Effect 0x10263e 14 1)
      [.gpr 1] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10263e 14 1).toInstrSpec (mov_r64_r64_effect_step 0x10263e 0x49 0xce (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x102641 [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x102641) (movR64R64Effect 0x102641 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x102641 15 2).toInstrSpec (mov_r64_r64_effect_step 0x102641 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x102644 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x102644) (movR64R64Effect 0x102644 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x102644 3 7).toInstrSpec (mov_r64_r64_effect_step 0x102644 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x102647 [0x48, 0x8D, 0x7C, 0x24, 0x20] (fun s => s.RIP = 0x102647) (leaR64Effect 0x102647 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102647 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x102647 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10264c [0xE8, 0x7F, 0x47, 0x00, 0x00] (PushPre 0x10264c 5) (callEffect (fun _ => 0x106dd0) 0x102651)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10264c 0x106dd0 0x102651).toInstrSpec (call_rel32_effect_step 0x10264c 0x477f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102632) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102634) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102636) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102637) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10263e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102641) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102644) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 61), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102647) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 61), (5, 5), (6, 6), (7, 69), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10264c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 71), (5, 5), (6, 6), (7, 69), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dd0) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l102630 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102630 :=
  Rest.liftedBlock (rest_l102630 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102630 x hx)

theorem rest_l102651 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102651 bytes_l102651) (entryMap (live .l102651))
      2 0x102651 bytes_l102651 b_l102651 := by
  have f0 : InstrSpec 0x102651 [0x83, 0x7C, 0x24, 0x20, 0x01] (LoadPre 0x102651 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x102651 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x102651 5 32 (.sib 4 none 0 (.d8 0x20)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x102651 5 (.sib 4 none 0 (.d8 0x20)) 0x1).toInstrSpec (cmp_m32_imm8_effect_step 0x102651 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102656) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x102656 4 0x227) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102651 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102651 :=
  Rest.liftedBlock (rest_l102651 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102651 x hx)

theorem rest_l10265c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10265c bytes_l10265c) (entryMap (live .l10265c))
      12 0x10265c bytes_l10265c b_l10265c := by
  have f0 : InstrSpec 0x10265c [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x10265c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10265c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10265c 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10265c 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10265c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x102661 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x102661 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102661 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102661 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102661 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x102661 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x102666 [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x102666 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x102666 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102666 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102666 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x102666 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10266b [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x10266b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10266b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10266b 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10266b 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10266b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x102670 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x102670 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x102670 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102670 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102670 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x102670 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x102675 [0x48, 0x8B, 0x4C, 0x24, 0x30] (LoadPre 0x102675 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x102675 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102675 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x102675 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x102675 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10267a [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x10267a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10267a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10267a 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10267a 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10267a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10267f [0x48, 0x89, 0x04, 0x24] (StorePre 0x10267f 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10267f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10267f 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10267f 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10267f 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x102683 [0x4C, 0x8D, 0xA4, 0x24, 0xC8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102683) (leaR64Effect 0x102683 12 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x102683 12 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (lea_r64_effect_step 0x102683 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10268b [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x10268b) (movR64R64Effect 0x10268b 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10268b 6 4).toInstrSpec (mov_r64_r64_effect_step 0x10268b 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10268e [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x10268e) (movR64R64Effect 0x10268e 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10268e 7 12).toInstrSpec (mov_r64_r64_effect_step 0x10268e 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x102691 [0xE8, 0xEA, 0xC7, 0x00, 0x00] (PushPre 0x102691 5) (callEffect (fun _ => 0x10ee80) 0x102696)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102691 0x10ee80 0x102696).toInstrSpec (call_rel32_effect_step 0x102691 0xc7ea (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102661) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102666) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10266b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102670) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102675) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10267a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10267f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102683) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10268b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 67), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10268e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 69), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102691) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 71), (5, 5), (6, 67), (7, 69), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee80) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l10265c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10265c :=
  Rest.liftedBlock (rest_l10265c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10265c x hx)

theorem rest_l102696 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102696 bytes_l102696) (entryMap (live .l102696))
      3 0x102696 bytes_l102696 b_l102696 := by
  have f0 : InstrSpec 0x102696 [0x48, 0x8D, 0xBC, 0x24, 0x60, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102696) (leaR64Effect 0x102696 7 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102696 7 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (lea_r64_effect_step 0x102696 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10269e [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x10269e) (movR64R64Effect 0x10269e 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10269e 6 12).toInstrSpec (mov_r64_r64_effect_step 0x10269e 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1026a1 [0xE8, 0xAA, 0xD7, 0x00, 0x00] (PushPre 0x1026a1 5) (callEffect (fun _ => 0x10fe50) 0x1026a6)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1026a1 0x10fe50 0x1026a6).toInstrSpec (call_rel32_effect_step 0x1026a1 0xd7aa (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10269e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026a1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe50) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l102696 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102696 :=
  Rest.liftedBlock (rest_l102696 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102696 x hx)

theorem rest_l1026a6_1 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 81) code lifted (codeRange 0x1026a6 bytes_l1026a6) [(0, 78), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      17 0x10273d bytes_l1026a6_1 b_l1026a6_1 := by
  have f20 : InstrSpec 0x10273d [0x48, 0x8D, 0x44, 0x24, 0x50] (fun s => s.RIP = 0x10273d) (leaR64Effect 0x10273d 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x10273d 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x10273d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x102742 [0x48, 0x8D, 0xB4, 0x24, 0x40, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102742) (leaR64Effect 0x102742 6 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102742 6 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (lea_r64_effect_step 0x102742 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10274a [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10274a) (movR32Imm32Effect 0x10274a 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10274a 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10274a 0xb9 (by decide) 0xf) pre_rip
  have f23 : InstrSpec 0x10274f [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x10274f) (movR64R64Effect 0x10274f 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10274f 7 0).toInstrSpec (mov_r64_r64_effect_step 0x10274f 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x102752 [0xF3, 0x48, 0xA5] (RepPre 0x102752 (RepMovsqPre 0x102752)) (repMovsqEffect 0x102752)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x102752).toInstrSpecOfRuns (rep_movsq_runs hstride 0x102752 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f25 : InstrSpec 0x102755 [0x4C, 0x8D, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102755) (leaR64Effect 0x102755 8 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x102755 8 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (lea_r64_effect_step 0x102755 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10275d [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10275d) (movR32Imm32Effect 0x10275d 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10275d 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10275d 0xb9 (by decide) 0xf) pre_rip
  have f27 : InstrSpec 0x102762 [0x4C, 0x89, 0xC7] (fun s => s.RIP = 0x102762) (movR64R64Effect 0x102762 7 8)
      [.gpr 8] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102762 7 8).toInstrSpec (mov_r64_r64_effect_step 0x102762 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x102765 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x102765) (movR64R64Effect 0x102765 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102765 6 0).toInstrSpec (mov_r64_r64_effect_step 0x102765 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x102768 [0xF3, 0x48, 0xA5] (RepPre 0x102768 (RepMovsqPre 0x102768)) (repMovsqEffect 0x102768)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x102768).toInstrSpecOfRuns (rep_movsq_runs hstride 0x102768 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f30 : InstrSpec 0x10276b [0x4C, 0x89, 0xBC, 0x24, 0x40, 0x01, 0x00, 0x00] (StorePre 0x10276b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10276b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10276b 15 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10276b 15 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_m64_r64_effect_step 0x10276b 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x102773 [0x4C, 0x89, 0xB4, 0x24, 0x48, 0x01, 0x00, 0x00] (StorePre 0x102773 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x102773 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102773 14 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102773 14 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (mov_m64_r64_effect_step 0x102773 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x10277b [0x48, 0x8D, 0x7C, 0x24, 0x48] (fun s => s.RIP = 0x10277b) (leaR64Effect 0x10277b 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10277b 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x10277b 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x102780 [0x48, 0x8D, 0x94, 0x24, 0x40, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102780) (leaR64Effect 0x102780 2 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x102780 2 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (lea_r64_effect_step 0x102780 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x102788 [0xB9, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102788) (movR32Imm32Effect 0x102788 5 1 0x1)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x102788 5 1 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x102788 0xb9 (by decide) 0x1) pre_rip
  have f35 : InstrSpec 0x10278d [0x4C, 0x89, 0xC6] (fun s => s.RIP = 0x10278d) (movR64R64Effect 0x10278d 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10278d 6 8).toInstrSpec (mov_r64_r64_effect_step 0x10278d 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x102790 [0xE8, 0x8B, 0x2C, 0x00, 0x00] (PushPre 0x102790 5) (callEffect (fun _ => 0x105420) 0x102795)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102790 0x105420 0x102795).toInstrSpec (call_rel32_effect_step 0x102790 0x2c8b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102742) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 81), (1, 55), (3, 3), (4, 4), (5, 5), (6, 83), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10274a) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 81), (1, 85), (3, 3), (4, 4), (5, 5), (6, 83), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10274f) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f23 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 81), (1, 85), (3, 3), (4, 4), (5, 5), (6, 83), (7, 87), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102752) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 81), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102755) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f25 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 81), (3, 3), (4, 4), (5, 5), (8, 90), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10275d) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 81), (1, 92), (3, 3), (4, 4), (5, 5), (8, 90), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102762) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f27 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 81), (1, 92), (3, 3), (4, 4), (5, 5), (7, 94), (8, 90), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102765) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f28 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 81), (1, 92), (3, 3), (4, 4), (5, 5), (6, 96), (7, 94), (8, 90), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102768) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 81), (3, 3), (4, 4), (5, 5), (8, 90), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10276b) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 81), (3, 3), (4, 4), (5, 5), (8, 90), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102773) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 81), (3, 3), (4, 4), (5, 5), (8, 90), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10277b) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f32 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 81), (3, 3), (4, 4), (5, 5), (7, 101), (8, 90), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102780) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f33 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 81), (2, 103), (3, 3), (4, 4), (5, 5), (7, 101), (8, 90), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102788) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f34 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 81), (1, 105), (2, 103), (3, 3), (4, 4), (5, 5), (7, 101), (8, 90), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10278d) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f35 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 81), (1, 105), (2, 103), (3, 3), (4, 4), (5, 5), (6, 107), (7, 101), (8, 90), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102790) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f36 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 81), (1, 105), (2, 103), (3, 3), (4, 109), (5, 5), (6, 107), (7, 101), (8, 90), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105420) f36 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 111) (by decide) (by decide) rfl rfl

theorem rest_l1026a6 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1026a6 bytes_l1026a6) (entryMap (live .l1026a6))
      37 0x1026a6 bytes_l1026a6 b_l1026a6 := by
  have f0 : InstrSpec 0x1026a6 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x1026a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1026a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026a6 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1026a6 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1026a6 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1026ab [0x48, 0x8B, 0x4C, 0x24, 0x30] (LoadPre 0x1026ab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1026ab + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026ab 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1026ab 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1026ab 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1026b0 [0x48, 0x89, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00] (StorePre 0x1026b0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1026b0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1026b0 0 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1026b0 0 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_m64_r64_effect_step 0x1026b0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1026b8 [0x48, 0x89, 0x8C, 0x24, 0x48, 0x01, 0x00, 0x00] (StorePre 0x1026b8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x1026b8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1026b8 1 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1026b8 1 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (mov_m64_r64_effect_step 0x1026b8 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1026c0 [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x1026c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1026c0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026c0 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1026c0 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1026c0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1026c5 [0x48, 0x89, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00] (StorePre 0x1026c5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x1026c5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1026c5 0 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1026c5 0 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (mov_m64_r64_effect_step 0x1026c5 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1026cd [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x1026cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1026cd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026cd 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1026cd 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1026cd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1026d2 [0x48, 0x89, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00] (StorePre 0x1026d2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x1026d2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1026d2 0 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1026d2 0 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (mov_m64_r64_effect_step 0x1026d2 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1026da [0x48, 0xC7, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1026da 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1026da + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1026da (.sib 4 none 0 (.d32 0xc8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1026da (.sib 4 none 0 (.d32 0xc8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1026da 0x48 (by decide) (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1026e6 [0x48, 0xC7, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1026e6 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1026e6 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1026e6 (.sib 4 none 0 (.d32 0xd0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1026e6 (.sib 4 none 0 (.d32 0xd0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1026e6 0x48 (by decide) (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1026f2 [0x48, 0xC7, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1026f2 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1026f2 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1026f2 (.sib 4 none 0 (.d32 0xd8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1026f2 (.sib 4 none 0 (.d32 0xd8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1026f2 0x48 (by decide) (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1026fe [0x48, 0xC7, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1026fe 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1026fe + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1026fe (.sib 4 none 0 (.d32 0xe0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1026fe (.sib 4 none 0 (.d32 0xe0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1026fe 0x48 (by decide) (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10270a [0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x10270a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10270a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10270a 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10270a 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x10270a 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x102712 [0x48, 0x89, 0x04, 0x24] (StorePre 0x102712 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102712 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102712 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102712 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x102712 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x102716 [0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (LoadPre 0x102716 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x102716 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102716 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102716 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x102716 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x10271e [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x10271e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10271e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10271e 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10271e 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10271e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x102723 [0x48, 0x8B, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x102723 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x102723 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102723 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102723 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x102723 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10272b [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x10272b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10272b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10272b 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10272b 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10272b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x102730 [0x48, 0x8B, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00] (LoadPre 0x102730 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x102730 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102730 0 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102730 0 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_r64_m64_effect_step 0x102730 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x102738 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x102738 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102738 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102738 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102738 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x102738 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026ab) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026b0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026b8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026c0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026c5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026cd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026d2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026da) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026e6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026f2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026fe) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10270a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102712) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102716) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10271e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102723) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10272b) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102730) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102738) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 78), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10273d) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1026a6_1 hstride code

theorem block_l1026a6 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1026a6 :=
  Rest.liftedBlock (rest_l1026a6 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1026a6 x hx)

theorem rest_l102795 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102795 bytes_l102795) (entryMap (live .l102795))
      2 0x102795 bytes_l102795 b_l102795 := by
  have f0 : InstrSpec 0x102795 [0x83, 0x7C, 0x24, 0x48, 0x01] (LoadPre 0x102795 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x102795 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x102795 5 32 (.sib 4 none 0 (.d8 0x48)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x102795 5 (.sib 4 none 0 (.d8 0x48)) 0x1).toInstrSpec (cmp_m32_imm8_effect_step 0x102795 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10279a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x10279a 5 0x1b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102795 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102795 :=
  Rest.liftedBlock (rest_l102795 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102795 x hx)

theorem rest_l10279c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10279c bytes_l10279c) (entryMap (live .l10279c))
      3 0x10279c bytes_l10279c b_l10279c := by
  have f0 : InstrSpec 0x10279c [0x48, 0x8B, 0x7C, 0x24, 0x50] (LoadPre 0x10279c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10279c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10279c 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10279c 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x10279c 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1027a1 [0x48, 0x85, 0xFF] (fun s => s.RIP = 0x1027a1) (testR64R64Effect 0x1027a1 7 7)
      [.gpr 7, .gpr 7] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1027a1 7 7).toInstrSpec (test_r64_r64_effect_step 0x1027a1 0x48 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027a1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027a4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1027a4 4 0x76) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10279c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10279c :=
  Rest.liftedBlock (rest_l10279c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10279c x hx)

theorem rest_l1027a6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1027a6 bytes_l1027a6) (entryMap (live .l1027a6))
      4 0x1027a6 bytes_l1027a6 b_l1027a6 := by
  have f0 : InstrSpec 0x1027a6 [0x48, 0x8B, 0x44, 0x24, 0x58] (LoadPre 0x1027a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1027a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1027a6 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1027a6 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x1027a6 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1027ab [0x48, 0x8B, 0x00] (LoadPre 0x1027ab (fun s => AddrMode.addr (.base 0 .none) s (0x1027ab + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1027ab 0 (.base 0 .none))
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1027ab 0 (.base 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1027ab 0x48 (by decide) 0 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1027ae [0x48, 0x85, 0xC0] (fun s => s.RIP = 0x1027ae) (testR64R64Effect 0x1027ae 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1027ae 0 0).toInstrSpec (test_r64_r64_effect_step 0x1027ae 0x48 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027ab) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027ae) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027b1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x1027b1 4 0x69) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1027a6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1027a6 :=
  Rest.liftedBlock (rest_l1027a6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1027a6 x hx)

theorem rest_l1027b3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1027b3 bytes_l1027b3) (entryMap (live .l1027b3))
      0 0x1027b3 bytes_l1027b3 b_l1027b3 := by
  exact Rest.cut

theorem block_l1027b3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1027b3 :=
  Rest.liftedBlock (rest_l1027b3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1027b3 x hx)

theorem rest_l1027b5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1027b5 bytes_l1027b5) (entryMap (live .l1027b5))
      1 0x1027b5 bytes_l1027b5 b_l1027b5 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x1027b5 0x65 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1027b5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1027b5 :=
  Rest.liftedBlock (rest_l1027b5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1027b5 x hx)

theorem rest_l1027b7_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x1027b7 bytes_l1027b7) [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x10280c bytes_l1027b7_1 b_l1027b7_1 := by
  have f20 : InstrSpec 0x10280c [0x48, 0x89, 0x7B, 0x20] (StorePre 0x10280c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x10280c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10280c 7 (.base 3 (.d8 0x20)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10280c 7 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10280c 0x48 (by decide) 7 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x102810 [0x4C, 0x89, 0x43, 0x28] (StorePre 0x102810 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x102810 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102810 8 (.base 3 (.d8 0x28)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x102810 8 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x102810 0x4c (by decide) 0 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x102814 [0x4C, 0x89, 0x4B, 0x30] (StorePre 0x102814 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x102814 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102814 9 (.base 3 (.d8 0x30)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x102814 9 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x102814 0x4c (by decide) 1 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x102818 [0x4C, 0x89, 0x53, 0x38] (StorePre 0x102818 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x102818 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102818 10 (.base 3 (.d8 0x38)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x102818 10 (.base 3 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x102818 0x4c (by decide) 2 (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102810) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102814) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102818) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10281c) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 93) (by decide) rfl

theorem rest_l1027b7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1027b7 bytes_l1027b7) (entryMap (live .l1027b7))
      24 0x1027b7 bytes_l1027b7 b_l1027b7 := by
  have f0 : InstrSpec 0x1027b7 [0x48, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x1027b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1027b7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1027b7 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1027b7 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x1027b7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1027bc [0x48, 0x0F, 0xC8] (fun s => s.RIP = 0x1027bc) (bswapR64Effect 0x1027bc 3 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (bswapR64Effect_footprint 0x1027bc 3 0).toInstrSpec (bswap_r64_effect_step 0x1027bc 0x48 (by decide) 0xc8 (by decide)) pre_rip
  have f2 : InstrSpec 0x1027bf [0x48, 0x8B, 0x4C, 0x24, 0x60] (LoadPre 0x1027bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1027bf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1027bf 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1027bf 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x1027bf 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1027c4 [0x48, 0x0F, 0xC9] (fun s => s.RIP = 0x1027c4) (bswapR64Effect 0x1027c4 3 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR64Effect_footprint 0x1027c4 3 1).toInstrSpec (bswap_r64_effect_step 0x1027c4 0x48 (by decide) 0xc9 (by decide)) pre_rip
  have f4 : InstrSpec 0x1027c7 [0x48, 0x8B, 0x54, 0x24, 0x50] (LoadPre 0x1027c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1027c7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1027c7 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1027c7 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x1027c7 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1027cc [0x48, 0x8B, 0x74, 0x24, 0x58] (LoadPre 0x1027cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1027cc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1027cc 6 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1027cc 6 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x1027cc 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1027d1 [0x48, 0x0F, 0xCE] (fun s => s.RIP = 0x1027d1) (bswapR64Effect 0x1027d1 3 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (bswapR64Effect_footprint 0x1027d1 3 6).toInstrSpec (bswap_r64_effect_step 0x1027d1 0x48 (by decide) 0xce (by decide)) pre_rip
  have f7 : InstrSpec 0x1027d4 [0x48, 0x0F, 0xCA] (fun s => s.RIP = 0x1027d4) (bswapR64Effect 0x1027d4 3 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR64Effect_footprint 0x1027d4 3 2).toInstrSpec (bswap_r64_effect_step 0x1027d4 0x48 (by decide) 0xca (by decide)) pre_rip
  have f8 : InstrSpec 0x1027d7 [0x48, 0x8B, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x1027d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1027d7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1027d7 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1027d7 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x1027d7 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1027df [0x48, 0x0F, 0xCF] (fun s => s.RIP = 0x1027df) (bswapR64Effect 0x1027df 3 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (bswapR64Effect_footprint 0x1027df 3 7).toInstrSpec (bswap_r64_effect_step 0x1027df 0x48 (by decide) 0xcf (by decide)) pre_rip
  have f10 : InstrSpec 0x1027e2 [0x4C, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x1027e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1027e2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1027e2 8 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1027e2 8 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x1027e2 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1027ea [0x49, 0x0F, 0xC8] (fun s => s.RIP = 0x1027ea) (bswapR64Effect 0x1027ea 3 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (bswapR64Effect_footprint 0x1027ea 3 8).toInstrSpec (bswap_r64_effect_step 0x1027ea 0x49 (by decide) 0xc8 (by decide)) pre_rip
  have f12 : InstrSpec 0x1027ed [0x4C, 0x8B, 0x4C, 0x24, 0x78] (LoadPre 0x1027ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1027ed + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1027ed 9 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1027ed 9 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x1027ed 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1027f2 [0x49, 0x0F, 0xC9] (fun s => s.RIP = 0x1027f2) (bswapR64Effect 0x1027f2 3 9)
      [.gpr 9] [] [.reg 9, .rip] :=
    (bswapR64Effect_footprint 0x1027f2 3 9).toInstrSpec (bswap_r64_effect_step 0x1027f2 0x49 (by decide) 0xc9 (by decide)) pre_rip
  have f14 : InstrSpec 0x1027f5 [0x4C, 0x8B, 0x54, 0x24, 0x70] (LoadPre 0x1027f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1027f5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1027f5 10 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1027f5 10 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x1027f5 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1027fa [0x49, 0x0F, 0xCA] (fun s => s.RIP = 0x1027fa) (bswapR64Effect 0x1027fa 3 10)
      [.gpr 10] [] [.reg 10, .rip] :=
    (bswapR64Effect_footprint 0x1027fa 3 10).toInstrSpec (bswap_r64_effect_step 0x1027fa 0x49 (by decide) 0xca (by decide)) pre_rip
  have f16 : InstrSpec 0x1027fd [0x48, 0x89, 0x03] (StorePre 0x1027fd 3 (fun s => AddrMode.addr (.base 3 .none) s (0x1027fd + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1027fd 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1027fd 0 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1027fd 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x102800 [0x48, 0x89, 0x4B, 0x08] (StorePre 0x102800 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x102800 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102800 1 (.base 3 (.d8 0x8)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x102800 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x102800 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x102804 [0x48, 0x89, 0x73, 0x10] (StorePre 0x102804 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x102804 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102804 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x102804 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x102804 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x102808 [0x48, 0x89, 0x53, 0x18] (StorePre 0x102808 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x102808 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102808 2 (.base 3 (.d8 0x18)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x102808 2 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x102808 0x48 (by decide) 2 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027bc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027bf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027c4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 59), (3, 3), (4, 4), (5, 5), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027c7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027cc) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 63), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027d1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 65), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027d4) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027d7) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 69), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027df) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027e2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 73), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027ea) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027ed) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 77), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027f2) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027f5) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 81), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027fa) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027fd) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102800) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102804) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102808) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10280c) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1027b7_1 code

theorem block_l1027b7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1027b7 :=
  Rest.liftedBlock (rest_l1027b7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1027b7 x hx)

theorem rest_l10281c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10281c bytes_l10281c) (entryMap (live .l10281c))
      18 0x10281c bytes_l10281c b_l10281c := by
  have f0 : InstrSpec 0x10281c [0x48, 0xC7, 0x44, 0x24, 0x48, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10281c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10281c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10281c (.sib 4 none 0 (.d8 0x48)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10281c (.sib 4 none 0 (.d8 0x48)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10281c 0x48 (by decide) (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x102825 [0x48, 0xC7, 0x44, 0x24, 0x50, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102825 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x102825 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102825 (.sib 4 none 0 (.d8 0x50)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102825 (.sib 4 none 0 (.d8 0x50)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102825 0x48 (by decide) (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10282e [0x48, 0xC7, 0x44, 0x24, 0x58, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10282e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10282e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10282e (.sib 4 none 0 (.d8 0x58)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10282e (.sib 4 none 0 (.d8 0x58)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10282e 0x48 (by decide) (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x102837 [0x48, 0xC7, 0x44, 0x24, 0x60, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102837 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x102837 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102837 (.sib 4 none 0 (.d8 0x60)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102837 (.sib 4 none 0 (.d8 0x60)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102837 0x48 (by decide) (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x102840 [0x48, 0x8B, 0x44, 0x24, 0x48] (LoadPre 0x102840 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x102840 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102840 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102840 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x102840 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x102845 [0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x102845 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x102845 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102845 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102845 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x102845 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10284d [0x48, 0x8B, 0x44, 0x24, 0x50] (LoadPre 0x10284d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10284d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10284d 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10284d 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x10284d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x102852 [0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x102852 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x102852 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102852 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102852 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x102852 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10285a [0x48, 0x8B, 0x44, 0x24, 0x58] (LoadPre 0x10285a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10285a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10285a 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10285a 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x10285a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10285f [0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x10285f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10285f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10285f 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10285f 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x10285f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x102867 [0x48, 0x8B, 0x44, 0x24, 0x60] (LoadPre 0x102867 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x102867 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102867 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102867 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x102867 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10286c [0x48, 0x89, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x10286c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10286c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10286c 0 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10286c 0 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x10286c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x102874 [0x48, 0x81, 0xC4, 0xB8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102874) (addR64Imm32Effect 0x102874 4 0x1b8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x102874 4 0x1b8).toInstrSpec (add_r64_imm32_effect_step 0x102874 0x48 0xc4 0x1b8 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10287b [0x5B] (PopPre 0x10287b) (popR64Effect 0x10287b 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10287b 1 3).toInstrSpec (pop_r64_effect_step 0x10287b 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f14 : InstrSpec 0x10287c [0x41, 0x5C] (PopPre 0x10287c) (popR64Effect 0x10287c 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10287c 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10287c 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f15 : InstrSpec 0x10287e [0x41, 0x5E] (PopPre 0x10287e) (popR64Effect 0x10287e 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10287e 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10287e 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f16 : InstrSpec 0x102880 [0x41, 0x5F] (PopPre 0x102880) (popR64Effect 0x102880 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102880 2 15).toInstrSpec (pop_r64_rex_effect_step 0x102880 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f17 : InstrSpec 0x102882 [0xC3] (RetPre 0x102882) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x102882).toInstrSpec (ret_effect_step 0x102882) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102825) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10282e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102837) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102840) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102845) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 57), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10284d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102852) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10285a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10285f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102867) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10286c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102874) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 66), (1, 1), (2, 2), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10287b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 66), (1, 1), (2, 2), (3, 71), (4, 72), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10287c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 75) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 76) (ρ' := [(0, 66), (1, 1), (2, 2), (3, 71), (4, 75), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10287e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f15 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 78) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 79) (ρ' := [(0, 66), (1, 1), (2, 2), (3, 71), (4, 78), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 13), (14, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102880) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 81) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 82) (ρ' := [(0, 66), (1, 1), (2, 2), (3, 71), (4, 81), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 13), (14, 77), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102882) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 84) f17 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 85) (ρ' := [(0, 66), (1, 1), (2, 2), (3, 71), (4, 84), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 13), (14, 77), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) f17 (by decide) rfl rfl rfl (by decide)

theorem block_l10281c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10281c :=
  Rest.liftedBlock (rest_l10281c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10281c x hx)

theorem rest_l102883 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102883 bytes_l102883) (entryMap (live .l102883))
      4 0x102883 bytes_l102883 b_l102883 := by
  have f0 : InstrSpec 0x102883 [0x48, 0xC7, 0x44, 0x24, 0x50, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102883 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x102883 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102883 (.sib 4 none 0 (.d8 0x50)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102883 (.sib 4 none 0 (.d8 0x50)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102883 0x48 (by decide) (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10288c [0x48, 0xC7, 0x44, 0x24, 0x48, 0x01, 0x00, 0x00, 0x00] (StorePre 0x10288c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10288c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10288c (.sib 4 none 0 (.d8 0x48)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10288c (.sib 4 none 0 (.d8 0x48)) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x10288c 0x48 (by decide) (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x102895 [0x48, 0x8D, 0x7C, 0x24, 0x48] (fun s => s.RIP = 0x102895) (leaR64Effect 0x102895 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102895 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x102895 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10289a [0xE8, 0x01, 0xD9, 0xFF, 0xFF] (PushPre 0x10289a 5) (callEffect (fun _ => 0x1001a0) 0x10289f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10289a 0x1001a0 0x10289f).toInstrSpec (call_rel32_effect_step 0x10289a 0xffffd901 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10288c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102895) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10289a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001a0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l102883 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102883 :=
  Rest.liftedBlock (rest_l102883 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102883 x hx)

theorem rest_l10289f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10289f bytes_l10289f) (entryMap (live .l10289f))
      1 0x10289f bytes_l10289f b_l10289f := by
  have f0 : InstrSpec 0x10289f [0xE8, 0x8C, 0xE1, 0xFF, 0xFF] (PushPre 0x10289f 5) (callEffect (fun _ => 0x100a30) 0x1028a4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10289f 0x100a30 0x1028a4).toInstrSpec (call_rel32_effect_step 0x10289f 0xffffe18c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := []) (p' := 0x100a30) f0 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 54) (by decide) (by decide) rfl rfl

theorem block_l10289f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10289f :=
  Rest.liftedBlock (rest_l10289f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10289f x hx)

theorem rest_l1028a4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1028a4 bytes_l1028a4) (entryMap (live .l1028a4))
      15 0x1028a4 bytes_l1028a4 b_l1028a4 := by
  have f0 : InstrSpec 0x1028a4 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1028a4) (fun _ => nopEffect 0x1028a4 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1028a4 10).toInstrSpec (nop_m_effect_step 0x1028a4 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1028ae [0x66, 0x90] (fun s => s.RIP = 0x1028ae) (fun _ => nopEffect 0x1028ae 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1028ae 2).toInstrSpec (nop_66_effect_step 0x1028ae) pre_rip
  have f2 : InstrSpec 0x1028b0 [0x55] (PushPre 0x1028b0 1) (pushR64Effect 0x1028b0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1028b0 1 5).toInstrSpec (push_r64_effect_step 0x1028b0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1028b1 [0x41, 0x57] (PushPre 0x1028b1 2) (pushR64Effect 0x1028b1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1028b1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1028b1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1028b3 [0x41, 0x56] (PushPre 0x1028b3 2) (pushR64Effect 0x1028b3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1028b3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1028b3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1028b5 [0x41, 0x54] (PushPre 0x1028b5 2) (pushR64Effect 0x1028b5 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1028b5 2 12).toInstrSpec (push_r64_rex_effect_step 0x1028b5 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1028b7 [0x53] (PushPre 0x1028b7 1) (pushR64Effect 0x1028b7 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1028b7 1 3).toInstrSpec (push_r64_effect_step 0x1028b7 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1028b8 [0x48, 0x81, 0xEC, 0x90, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x1028b8) (subR64Imm32Effect 0x1028b8 4 0x390)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x1028b8 4 0x390).toInstrSpec (sub_r64_imm32_effect_step 0x1028b8 0x48 0xec 0x390 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1028bf [0x44, 0x89, 0xC5] (fun s => s.RIP = 0x1028bf) (movR32R32Effect 0x1028bf 3 5 8)
      [.gpr 8] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x1028bf 3 5 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x1028bf 0x44 0xc5 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1028c2 [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x1028c2) (movR64R64Effect 0x1028c2 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1028c2 15 2).toInstrSpec (mov_r64_r64_effect_step 0x1028c2 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1028c5 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x1028c5) (movR64R64Effect 0x1028c5 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1028c5 14 6).toInstrSpec (mov_r64_r64_effect_step 0x1028c5 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1028c8 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x1028c8) (movR64R64Effect 0x1028c8 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1028c8 3 7).toInstrSpec (mov_r64_r64_effect_step 0x1028c8 0x48 0xfb (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1028cb [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x1028cb) (movR64R64Effect 0x1028cb 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1028cb 7 4).toInstrSpec (mov_r64_r64_effect_step 0x1028cb 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1028ce [0x48, 0x89, 0xCE] (fun s => s.RIP = 0x1028ce) (movR64R64Effect 0x1028ce 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1028ce 6 1).toInstrSpec (mov_r64_r64_effect_step 0x1028ce 0x48 0xce (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1028d1 [0xE8, 0xEA, 0x11, 0x00, 0x00] (PushPre 0x1028d1 5) (callEffect (fun _ => 0x103ac0) 0x1028d6)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1028d1 0x103ac0 0x1028d6).toInstrSpec (call_rel32_effect_step 0x1028d1 0x11ea (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028ae) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028b0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028b1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028b3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028b5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028b7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028b8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028bf) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028c2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028c5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028c8) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 73), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028cb) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 2), (3, 73), (4, 65), (5, 67), (6, 6), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028ce) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 1), (2, 2), (3, 73), (4, 65), (5, 67), (6, 77), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028d1) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 1), (2, 2), (3, 73), (4, 79), (5, 67), (6, 77), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ac0) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 81) (by decide) (by decide) rfl rfl

theorem block_l1028a4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1028a4 :=
  Rest.liftedBlock (rest_l1028a4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1028a4 x hx)

theorem rest_l1028d6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1028d6 bytes_l1028d6) (entryMap (live .l1028d6))
      2 0x1028d6 bytes_l1028d6 b_l1028d6 := by
  have f0 : InstrSpec 0x1028d6 [0x83, 0x3C, 0x24, 0x01] (LoadPre 0x1028d6 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1028d6 + BitVec.ofNat 64 4)) 4) (cmpMImm8Effect 0x1028d6 4 32 (.sib 4 none 0 .none) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x1028d6 4 (.sib 4 none 0 .none) 0x1).toInstrSpec (cmp_m32_imm8_effect_step 0x1028d6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028da) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1028da 4 0x6c7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1028d6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1028d6 :=
  Rest.liftedBlock (rest_l1028d6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1028d6 x hx)

theorem rest_l1028e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1028e0 bytes_l1028e0) (entryMap (live .l1028e0))
      18 0x1028e0 bytes_l1028e0 b_l1028e0 := by
  have f0 : InstrSpec 0x1028e0 [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x1028e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1028e0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1028e0 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1028e0 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1028e0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1028e5 [0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x1028e5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1028e5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1028e5 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1028e5 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x1028e5 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1028ed [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x1028ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1028ed + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1028ed 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1028ed 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1028ed 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1028f2 [0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x1028f2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1028f2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1028f2 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1028f2 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x1028f2 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1028fa [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x1028fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1028fa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1028fa 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1028fa 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1028fa 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1028ff [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x1028ff 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1028ff + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1028ff 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1028ff 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x1028ff 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x102907 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x102907 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x102907 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102907 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102907 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x102907 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10290c [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x10290c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10290c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10290c 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10290c 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x10290c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x102914 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x102914 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x102914 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102914 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102914 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x102914 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x102919 [0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x102919 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x102919 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102919 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102919 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x102919 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x102921 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x102921 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102921 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102921 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102921 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x102921 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x102926 [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x102926 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x102926 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102926 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102926 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x102926 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10292e [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x10292e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10292e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10292e 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10292e 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10292e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x102933 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x102933 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102933 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102933 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x102933 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x102933 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x102938 [0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x102938 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x102938 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102938 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102938 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x102938 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x102940 [0x48, 0x89, 0x44, 0x24, 0x78] (StorePre 0x102940 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x102940 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102940 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102940 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x102940 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x102945 [0x40, 0x80, 0xFD, 0x04] (fun s => s.RIP = 0x102945) (cmpR8Imm8Effect 0x102945 4 5 0x4)
      [.gpr 5] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x102945 4 5 0x4).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x102945 0x40 0xfd 0x4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028e5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028ed) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028f2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028fa) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028ff) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102907) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10290c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102914) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102919) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102921) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102926) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10292e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102933) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102938) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102940) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102945) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102949) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 79) (jcc_rel32_effect_step 0x102949 3 0x660) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1028e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1028e0 :=
  Rest.liftedBlock (rest_l1028e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1028e0 x hx)

theorem rest_l10294f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10294f bytes_l10294f) (entryMap (live .l10294f))
      15 0x10294f bytes_l10294f b_l10294f := by
  have f0 : InstrSpec 0x10294f [0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x10294f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10294f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10294f 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10294f 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x10294f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x102957 [0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x102957 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x102957 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102957 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102957 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x102957 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10295f [0x48, 0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x10295f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10295f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10295f 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10295f 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x10295f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x102967 [0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x102967 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x102967 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102967 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102967 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x102967 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10296f [0x48, 0x8B, 0x44, 0x24, 0x78] (LoadPre 0x10296f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10296f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10296f 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10296f 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x10296f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x102974 [0x48, 0x8B, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x102974 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x102974 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102974 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x102974 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x102974 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10297c [0x48, 0x89, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x10297c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10297c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10297c 1 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10297c 1 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x10297c 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x102984 [0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x102984 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x102984 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102984 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102984 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x102984 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10298c [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10298c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10298c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10298c (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10298c (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10298c 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x102995 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102995 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102995 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102995 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102995 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102995 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10299e [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10299e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10299e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10299e (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10299e (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10299e 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1029a7 [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1029a7 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1029a7 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1029a7 (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1029a7 (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1029a7 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1029af [0x48, 0x8D, 0xBC, 0x24, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1029af) (leaR64Effect 0x1029af 7 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1029af 7 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (lea_r64_effect_step 0x1029af 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1029b7 [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x1029b7) (movR64R64Effect 0x1029b7 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1029b7 6 4).toInstrSpec (mov_r64_r64_effect_step 0x1029b7 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1029ba [0xE8, 0xC1, 0x78, 0x00, 0x00] (PushPre 0x1029ba 5) (callEffect (fun _ => 0x10a280) 0x1029bf)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1029ba 0x10a280 0x1029bf).toInstrSpec (call_rel32_effect_step 0x1029ba 0x78c1 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102957) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10295f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102967) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10296f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102974) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10297c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102984) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10298c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102995) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10299e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029a7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029af) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029b7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 71), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029ba) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 73), (5, 5), (6, 71), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a280) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l10294f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10294f :=
  Rest.liftedBlock (rest_l10294f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10294f x hx)

theorem rest_l1029bf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1029bf bytes_l1029bf) (entryMap (live .l1029bf))
      4 0x1029bf bytes_l1029bf b_l1029bf := by
  have f0 : InstrSpec 0x1029bf [0xF6, 0xD0] (fun s => s.RIP = 0x1029bf) (notR8Effect 0x1029bf 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR8Effect_footprint 0x1029bf 2 0).toInstrSpec (not_r8_effect_step 0x1029bf 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1029c1 [0x24, 0x01] (fun s => s.RIP = 0x1029c1) (andAlImm8Effect 0x1029c1 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x1029c1 0x1).toInstrSpec (and_al_imm8_effect_step 0x1029c1 0x1) pre_rip
  have f2 : InstrSpec 0x1029c3 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x1029c3) (movzxR32R8Effect 0x1029c3 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x1029c3 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x1029c3 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1029c6 [0xE8, 0x85, 0x53, 0x02, 0x00] (PushPre 0x1029c6 5) (callEffect (fun _ => 0x127d50) 0x1029cb)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1029c6 0x127d50 0x1029cb).toInstrSpec (call_rel32_effect_step 0x1029c6 0x25385 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029c3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029c6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1029bf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1029bf :=
  Rest.liftedBlock (rest_l1029bf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1029bf x hx)

theorem rest_l1029cb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1029cb bytes_l1029cb) (entryMap (live .l1029cb))
      3 0x1029cb bytes_l1029cb b_l1029cb := by
  have f0 : InstrSpec 0x1029cb [0x88, 0x04, 0x24] (StorePre 0x1029cb 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1029cb + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1029cb 3 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1029cb 3 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x1029cb 0 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1029ce [0x3C, 0x01] (fun s => s.RIP = 0x1029ce) (cmpAlImm8Effect 0x1029ce 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x1029ce 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x1029ce 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029ce) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029d0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x1029d0 5 0x555) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1029cb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1029cb :=
  Rest.liftedBlock (rest_l1029cb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1029cb x hx)

theorem rest_l1029d6_1 [Bindings] (code : CodeMap) :
    Rest (n := 81) code lifted (codeRange 0x1029d6 bytes_l1029d6) [(0, 74), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      3 0x102a76 bytes_l1029d6_1 b_l1029d6_1 := by
  have f20 : InstrSpec 0x102a76 [0x48, 0x8D, 0xBC, 0x24, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102a76) (leaR64Effect 0x102a76 7 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102a76 7 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (lea_r64_effect_step 0x102a76 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x102a7e [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x102a7e) (movR64R64Effect 0x102a7e 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102a7e 6 4).toInstrSpec (mov_r64_r64_effect_step 0x102a7e 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x102a81 [0xE8, 0xFA, 0x77, 0x00, 0x00] (PushPre 0x102a81 5) (callEffect (fun _ => 0x10a280) 0x102a86)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102a81 0x10a280 0x102a86).toInstrSpec (call_rel32_effect_step 0x102a81 0x77fa (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f20 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 74), (1, 55), (3, 3), (4, 4), (5, 5), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a7e) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 74), (1, 55), (3, 3), (4, 4), (5, 5), (6, 83), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a81) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f22 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 74), (1, 55), (3, 3), (4, 85), (5, 5), (6, 83), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a280) f22 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 87) (by decide) (by decide) rfl rfl

theorem rest_l1029d6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1029d6 bytes_l1029d6) (entryMap (live .l1029d6))
      23 0x1029d6 bytes_l1029d6 b_l1029d6 := by
  have f0 : InstrSpec 0x1029d6 [0x48, 0x8B, 0x44, 0x24, 0x78] (LoadPre 0x1029d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1029d6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1029d6 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1029d6 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x1029d6 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1029db [0x48, 0x8B, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x1029db (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1029db + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1029db 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1029db 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x1029db 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1029e3 [0x48, 0x89, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00] (StorePre 0x1029e3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x1029e3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1029e3 0 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1029e3 0 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_m64_r64_effect_step 0x1029e3 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1029eb [0x48, 0x89, 0x8C, 0x24, 0x38, 0x01, 0x00, 0x00] (StorePre 0x1029eb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x1029eb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1029eb 1 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1029eb 1 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_m64_r64_effect_step 0x1029eb 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1029f3 [0x48, 0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x1029f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1029f3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1029f3 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1029f3 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x1029f3 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1029fb [0x48, 0x89, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00] (StorePre 0x1029fb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1029fb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1029fb 0 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1029fb 0 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_m64_r64_effect_step 0x1029fb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x102a03 [0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x102a03 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x102a03 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102a03 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102a03 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x102a03 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x102a0b [0x48, 0x89, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00] (StorePre 0x102a0b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x102a0b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102a0b 0 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102a0b 0 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (mov_m64_r64_effect_step 0x102a0b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x102a13 [0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x102a13 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x102a13 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102a13 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102a13 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x102a13 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x102a1b [0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x102a1b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x102a1b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102a1b 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102a1b 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x102a1b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x102a23 [0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x102a23 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x102a23 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102a23 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102a23 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x102a23 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x102a2b [0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x102a2b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x102a2b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102a2b 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102a2b 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x102a2b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x102a33 [0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x102a33 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x102a33 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102a33 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102a33 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x102a33 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x102a3b [0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x102a3b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x102a3b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102a3b 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102a3b 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x102a3b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x102a43 [0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x102a43 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x102a43 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102a43 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102a43 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x102a43 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x102a4b [0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x102a4b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x102a4b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102a4b 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102a4b 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x102a4b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x102a53 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102a53 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102a53 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102a53 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102a53 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102a53 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x102a5c [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102a5c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102a5c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102a5c (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102a5c (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102a5c 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x102a65 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102a65 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x102a65 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102a65 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102a65 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102a65 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x102a6e [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102a6e 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102a6e + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x102a6e (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102a6e (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102a6e 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029db) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029e3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029eb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029f3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029fb) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a03) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a0b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a13) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a1b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a23) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a2b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a33) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a3b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a43) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a4b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 74), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a53) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 74), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a5c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 74), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a65) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 74), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a6e) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 74), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a76) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1029d6_1 code

theorem block_l1029d6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1029d6 :=
  Rest.liftedBlock (rest_l1029d6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1029d6 x hx)

theorem rest_l102a86 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102a86 bytes_l102a86) (entryMap (live .l102a86))
      4 0x102a86 bytes_l102a86 b_l102a86 := by
  have f0 : InstrSpec 0x102a86 [0xF6, 0xD0] (fun s => s.RIP = 0x102a86) (notR8Effect 0x102a86 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR8Effect_footprint 0x102a86 2 0).toInstrSpec (not_r8_effect_step 0x102a86 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102a88 [0x24, 0x01] (fun s => s.RIP = 0x102a88) (andAlImm8Effect 0x102a88 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x102a88 0x1).toInstrSpec (and_al_imm8_effect_step 0x102a88 0x1) pre_rip
  have f2 : InstrSpec 0x102a8a [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x102a8a) (movzxR32R8Effect 0x102a8a 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x102a8a 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x102a8a 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102a8d [0xE8, 0xBE, 0x52, 0x02, 0x00] (PushPre 0x102a8d 5) (callEffect (fun _ => 0x127d50) 0x102a92)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102a8d 0x127d50 0x102a92).toInstrSpec (call_rel32_effect_step 0x102a8d 0x252be (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a88) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a8a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a8d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l102a86 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102a86 :=
  Rest.liftedBlock (rest_l102a86 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102a86 x hx)

theorem rest_l102a92 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102a92 bytes_l102a92) (entryMap (live .l102a92))
      3 0x102a92 bytes_l102a92 b_l102a92 := by
  have f0 : InstrSpec 0x102a92 [0x88, 0x04, 0x24] (StorePre 0x102a92 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102a92 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x102a92 3 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x102a92 3 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x102a92 0 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x102a95 [0x3C, 0x01] (fun s => s.RIP = 0x102a95) (cmpAlImm8Effect 0x102a95 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x102a95 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x102a95 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a95) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a97) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x102a97 5 0x48e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102a92 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102a92 :=
  Rest.liftedBlock (rest_l102a92 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102a92 x hx)

theorem rest_l102a9d_1 [Bindings] (code : CodeMap) :
    Rest (n := 82) code lifted (codeRange 0x102a9d bytes_l102a9d) [(0, 68), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (6, 77), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]
      7 0x102b17 bytes_l102a9d_1 b_l102a9d_1 := by
  have f20 : InstrSpec 0x102b17 [0x48, 0xC7, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102b17 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x102b17 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x102b17 (.sib 4 none 0 (.d32 0xc0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102b17 (.sib 4 none 0 (.d32 0xc0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102b17 0x48 (by decide) (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x102b23 [0x48, 0xC7, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102b23 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x102b23 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x102b23 (.sib 4 none 0 (.d32 0xb8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102b23 (.sib 4 none 0 (.d32 0xb8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102b23 0x48 (by decide) (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x102b2f [0x48, 0x8D, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102b2f) (leaR64Effect 0x102b2f 2 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x102b2f 2 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (lea_r64_effect_step 0x102b2f 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x102b37 [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102b37) (movR32Imm32Effect 0x102b37 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x102b37 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x102b37 0xb9 (by decide) 0x4) pre_rip
  have f24 : InstrSpec 0x102b3c [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x102b3c) (movR64R64Effect 0x102b3c 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102b3c 7 14).toInstrSpec (mov_r64_r64_effect_step 0x102b3c 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x102b3f [0x41, 0xB8, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102b3f) (movR32Imm32Effect 0x102b3f 6 8 0x100)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x102b3f 6 8 0x100).toInstrSpec (mov_r32_imm32_rex_effect_step 0x102b3f 0x41 0xb8 (by decide) (by decide) 0x100) pre_rip
  have f26 : InstrSpec 0x102b45 [0xE8, 0x26, 0x52, 0x02, 0x00] (PushPre 0x102b45 5) (callEffect (fun _ => 0x127d70) 0x102b4a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102b45 0x127d70 0x102b4a).toInstrSpec (call_rel32_effect_step 0x102b45 0x25226 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 68), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (6, 77), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b23) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 68), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (6, 77), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b2f) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 68), (1, 61), (2, 84), (3, 3), (4, 4), (5, 5), (6, 77), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b37) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 68), (1, 86), (2, 84), (3, 3), (4, 4), (5, 5), (6, 77), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b3c) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f24 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 68), (1, 86), (2, 84), (3, 3), (4, 4), (5, 5), (6, 77), (7, 88), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b3f) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f25 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 68), (1, 86), (2, 84), (3, 3), (4, 4), (5, 5), (6, 77), (7, 88), (8, 90), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b45) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f26 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 68), (1, 86), (2, 84), (3, 3), (4, 92), (5, 5), (6, 77), (7, 88), (8, 90), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d70) f26 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 94) (by decide) (by decide) rfl rfl

theorem rest_l102a9d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102a9d bytes_l102a9d) (entryMap (live .l102a9d))
      27 0x102a9d bytes_l102a9d b_l102a9d := by
  have f0 : InstrSpec 0x102a9d [0x48, 0x8D, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102a9d) (leaR64Effect 0x102a9d 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x102a9d 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (lea_r64_effect_step 0x102a9d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102aa5 [0x48, 0x8B, 0x08] (LoadPre 0x102aa5 (fun s => AddrMode.addr (.base 0 .none) s (0x102aa5 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x102aa5 1 (.base 0 .none))
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x102aa5 1 (.base 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x102aa5 0x48 (by decide) 1 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x102aa8 [0x48, 0x8B, 0x50, 0x08] (LoadPre 0x102aa8 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x102aa8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102aa8 2 (.base 0 (.d8 0x8)))
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x102aa8 2 (.base 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x102aa8 0x48 (by decide) 2 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x102aac [0x48, 0x89, 0x8C, 0x24, 0x90, 0x01, 0x00, 0x00] (StorePre 0x102aac 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x102aac + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102aac 1 (.sib 4 none 0 (.d32 0x190)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102aac 1 (.sib 4 none 0 (.d32 0x190))).toInstrSpec (mov_m64_r64_effect_step 0x102aac 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x190)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x102ab4 [0x48, 0x89, 0x94, 0x24, 0x98, 0x01, 0x00, 0x00] (StorePre 0x102ab4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x102ab4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102ab4 2 (.sib 4 none 0 (.d32 0x198)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102ab4 2 (.sib 4 none 0 (.d32 0x198))).toInstrSpec (mov_m64_r64_effect_step 0x102ab4 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x198)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x102abc [0x48, 0x8B, 0x48, 0x10] (LoadPre 0x102abc (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x102abc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102abc 1 (.base 0 (.d8 0x10)))
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x102abc 1 (.base 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x102abc 0x48 (by decide) 1 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x102ac0 [0x48, 0x89, 0x8C, 0x24, 0xA0, 0x01, 0x00, 0x00] (StorePre 0x102ac0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x102ac0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102ac0 1 (.sib 4 none 0 (.d32 0x1a0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102ac0 1 (.sib 4 none 0 (.d32 0x1a0))).toInstrSpec (mov_m64_r64_effect_step 0x102ac0 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1a0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x102ac8 [0x48, 0x8B, 0x40, 0x18] (LoadPre 0x102ac8 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x102ac8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102ac8 0 (.base 0 (.d8 0x18)))
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102ac8 0 (.base 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x102ac8 0x48 (by decide) 0 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x102acc [0x48, 0x89, 0x84, 0x24, 0xA8, 0x01, 0x00, 0x00] (StorePre 0x102acc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x102acc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102acc 0 (.sib 4 none 0 (.d32 0x1a8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102acc 0 (.sib 4 none 0 (.d32 0x1a8))).toInstrSpec (mov_m64_r64_effect_step 0x102acc 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1a8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x102ad4 [0xC6, 0x04, 0x24, 0x01] (StorePre 0x102ad4 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102ad4 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x102ad4 (.sib 4 none 0 .none) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x102ad4 (.sib 4 none 0 .none) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x102ad4 (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x102ad8 [0x48, 0x89, 0xE0] (fun s => s.RIP = 0x102ad8) (movR64R64Effect 0x102ad8 0 4)
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x102ad8 0 4).toInstrSpec (mov_r64_r64_effect_step 0x102ad8 0x48 0xe0 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x102adb [0xC6, 0x04, 0x24, 0x00] (StorePre 0x102adb 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102adb + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x102adb (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x102adb (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x102adb (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x102adf [0xC6, 0x04, 0x24, 0x00] (StorePre 0x102adf 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102adf + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x102adf (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x102adf (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x102adf (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x102ae3 [0xC6, 0x04, 0x24, 0x00] (StorePre 0x102ae3 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102ae3 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x102ae3 (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x102ae3 (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x102ae3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x102ae7 [0x49, 0x83, 0xFF, 0x20] (fun s => s.RIP = 0x102ae7) (cmpR64Imm8Effect 0x102ae7 15 0x20)
      [.gpr 15] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x102ae7 15 0x20).toInstrSpec (cmp_r64_imm8_effect_step 0x102ae7 0x49 0xff 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x102aeb [0xBE, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102aeb) (movR32Imm32Effect 0x102aeb 5 6 0x20)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x102aeb 5 6 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x102aeb 0xbe (by decide) 0x20) pre_rip
  have f16 : InstrSpec 0x102af0 [0x49, 0x0F, 0x42, 0xF7] (fun s => s.RIP = 0x102af0) (atFlags (condHolds 2) (cmovR64R64Effect 0x102af0 4 6 15))
      [.gpr 6, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .rip] :=
    (cmovR64R64Effect_footprint 0x102af0 4 6 15 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x102af0 2 0x49 (by decide) 0xf7 (by decide) c)) pre_rip
  have f17 : InstrSpec 0x102af4 [0xC7, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00] (StorePre 0x102af4 11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x102af4 + BitVec.ofNat 64 11)) 4) (movM32Imm32Effect 0x102af4 11 (.sib 4 none 0 (.d32 0x1d0)) 0x100)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x102af4 11 (.sib 4 none 0 (.d32 0x1d0)) 0x100).toInstrSpec (mov_m32_imm32_effect_step 0x102af4 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide) 0x100) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x102aff [0x48, 0xC7, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102aff 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x102aff + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x102aff (.sib 4 none 0 (.d32 0xd0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102aff (.sib 4 none 0 (.d32 0xd0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102aff 0x48 (by decide) (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x102b0b [0x48, 0xC7, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102b0b 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x102b0b + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x102b0b (.sib 4 none 0 (.d32 0xc8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102b0b (.sib 4 none 0 (.d32 0xc8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102b0b 0x48 (by decide) (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102aa5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102aa8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102aac) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ab4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102abc) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ac0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ac8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102acc) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ad4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ad8) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102adb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102adf) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 68), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ae3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 68), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ae7) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f14 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 68), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102aeb) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 68), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (6, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102af0) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 68), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (6, 77), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102af4) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 68), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (6, 77), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102aff) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 68), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (6, 77), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b0b) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 68), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (6, 77), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b17) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l102a9d_1 code

theorem block_l102a9d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102a9d :=
  Rest.liftedBlock (rest_l102a9d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102a9d x hx)

theorem rest_l102b4a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102b4a bytes_l102b4a) (entryMap (live .l102b4a))
      2 0x102b4a bytes_l102b4a b_l102b4a := by
  have f0 : InstrSpec 0x102b4a [0x3C, 0xFF] (fun s => s.RIP = 0x102b4a) (cmpAlImm8Effect 0x102b4a 0xff)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x102b4a 0xff).toInstrSpec (cmp_al_imm8_effect_step 0x102b4a 0xff) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b4c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x102b4c 5 0x3f3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102b4a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102b4a :=
  Rest.liftedBlock (rest_l102b4a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102b4a x hx)

theorem rest_l102b52 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102b52 bytes_l102b52) (entryMap (live .l102b52))
      11 0x102b52 bytes_l102b52 b_l102b52 := by
  have f0 : InstrSpec 0x102b52 [0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (LoadPre 0x102b52 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x102b52 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102b52 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102b52 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x102b52 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x102b5a [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x102b5a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102b5a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102b5a 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102b5a 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x102b5a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x102b5f [0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x102b5f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x102b5f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102b5f 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102b5f 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x102b5f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x102b67 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x102b67 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102b67 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102b67 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102b67 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x102b67 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x102b6c [0x48, 0x8B, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x102b6c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x102b6c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102b6c 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102b6c 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x102b6c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x102b74 [0x48, 0x8B, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x102b74 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x102b74 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102b74 1 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x102b74 1 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x102b74 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x102b7c [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x102b7c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x102b7c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102b7c 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102b7c 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x102b7c 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x102b81 [0x48, 0x89, 0x04, 0x24] (StorePre 0x102b81 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102b81 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102b81 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102b81 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x102b81 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x102b85 [0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102b85) (leaR64Effect 0x102b85 7 (.sib 4 none 0 (.d32 0x1b0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102b85 7 (.sib 4 none 0 (.d32 0x1b0))).toInstrSpec (lea_r64_effect_step 0x102b85 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x1b0)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x102b8d [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x102b8d) (movR64R64Effect 0x102b8d 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102b8d 6 4).toInstrSpec (mov_r64_r64_effect_step 0x102b8d 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x102b90 [0xE8, 0xEB, 0x73, 0x00, 0x00] (PushPre 0x102b90 5) (callEffect (fun _ => 0x109f80) 0x102b95)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102b90 0x109f80 0x102b95).toInstrSpec (call_rel32_effect_step 0x102b90 0x73eb (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b5a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b5f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b67) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b6c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b74) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b7c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b81) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b85) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b8d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b90) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f80) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l102b52 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102b52 :=
  Rest.liftedBlock (rest_l102b52 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102b52 x hx)

theorem rest_l102b95 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102b95 bytes_l102b95) (entryMap (live .l102b95))
      2 0x102b95 bytes_l102b95 b_l102b95 := by
  have f0 : InstrSpec 0x102b95 [0x40, 0x80, 0xFD, 0x01] (fun s => s.RIP = 0x102b95) (cmpR8Imm8Effect 0x102b95 4 5 0x1)
      [.gpr 5] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x102b95 4 5 0x1).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x102b95 0x40 0xfd 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b99) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x102b99 7 0x1a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102b95 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102b95 :=
  Rest.liftedBlock (rest_l102b95 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102b95 x hx)

theorem rest_l102b9b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102b9b bytes_l102b9b) (entryMap (live .l102b9b))
      3 0x102b9b bytes_l102b9b b_l102b9b := by
  have f0 : InstrSpec 0x102b9b [0x48, 0x8D, 0xBC, 0x24, 0x50, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102b9b) (leaR64Effect 0x102b9b 7 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102b9b 7 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (lea_r64_effect_step 0x102b9b 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102ba3 [0x48, 0x8D, 0xB4, 0x24, 0x30, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102ba3) (leaR64Effect 0x102ba3 6 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102ba3 6 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (lea_r64_effect_step 0x102ba3 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102bab [0xE8, 0x80, 0x72, 0x00, 0x00] (PushPre 0x102bab 5) (callEffect (fun _ => 0x109e30) 0x102bb0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102bab 0x109e30 0x102bb0).toInstrSpec (call_rel32_effect_step 0x102bab 0x7280 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ba3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bab) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e30) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l102b9b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102b9b :=
  Rest.liftedBlock (rest_l102b9b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102b9b x hx)

theorem rest_l102bb0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102bb0 bytes_l102bb0) (entryMap (live .l102bb0))
      1 0x102bb0 bytes_l102bb0 b_l102bb0 := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x102bb0 0x126 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l102bb0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102bb0 :=
  Rest.liftedBlock (rest_l102bb0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102bb0 x hx)

theorem rest_l102bb5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102bb5 bytes_l102bb5) (entryMap (live .l102bb5))
      4 0x102bb5 bytes_l102bb5 b_l102bb5 := by
  have f0 : InstrSpec 0x102bb5 [0x4C, 0x8D, 0xB4, 0x24, 0xD0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102bb5) (leaR64Effect 0x102bb5 14 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x102bb5 14 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (lea_r64_effect_step 0x102bb5 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102bbd [0x48, 0x8D, 0xB4, 0x24, 0x30, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102bbd) (leaR64Effect 0x102bbd 6 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102bbd 6 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (lea_r64_effect_step 0x102bbd 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102bc5 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x102bc5) (movR64R64Effect 0x102bc5 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102bc5 7 14).toInstrSpec (mov_r64_r64_effect_step 0x102bc5 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102bc8 [0xE8, 0x63, 0x72, 0x00, 0x00] (PushPre 0x102bc8 5) (callEffect (fun _ => 0x109e30) 0x102bcd)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102bc8 0x109e30 0x102bcd).toInstrSpec (call_rel32_effect_step 0x102bc8 0x7263 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bbd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bc5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bc8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 55), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e30) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l102bb5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102bb5 :=
  Rest.liftedBlock (rest_l102bb5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102bb5 x hx)

theorem rest_l102bcd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102bcd bytes_l102bcd) (entryMap (live .l102bcd))
      11 0x102bcd bytes_l102bcd b_l102bcd := by
  have f0 : InstrSpec 0x102bcd [0xC7, 0x84, 0x24, 0xF8, 0x02, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00] (StorePre 0x102bcd 11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2f8)) s (0x102bcd + BitVec.ofNat 64 11)) 4) (movM32Imm32Effect 0x102bcd 11 (.sib 4 none 0 (.d32 0x2f8)) 0x100)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x102bcd 11 (.sib 4 none 0 (.d32 0x2f8)) 0x100).toInstrSpec (mov_m32_imm32_effect_step 0x102bcd (.sib 4 none 0 (.d32 0x2f8)) (by decide) (by decide) (by decide) 0x100) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x102bd8 [0x48, 0xC7, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102bd8 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x102bd8 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x102bd8 (.sib 4 none 0 (.d32 0xd0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102bd8 (.sib 4 none 0 (.d32 0xd0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102bd8 0x48 (by decide) (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x102be4 [0x48, 0xC7, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102be4 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x102be4 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x102be4 (.sib 4 none 0 (.d32 0xc8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102be4 (.sib 4 none 0 (.d32 0xc8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102be4 0x48 (by decide) (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x102bf0 [0x48, 0xC7, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102bf0 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x102bf0 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x102bf0 (.sib 4 none 0 (.d32 0xc0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102bf0 (.sib 4 none 0 (.d32 0xc0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102bf0 0x48 (by decide) (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x102bfc [0x48, 0xC7, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102bfc 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x102bfc + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x102bfc (.sib 4 none 0 (.d32 0xb8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102bfc (.sib 4 none 0 (.d32 0xb8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102bfc 0x48 (by decide) (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x102c08 [0x48, 0x8D, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102c08) (leaR64Effect 0x102c08 2 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x102c08 2 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (lea_r64_effect_step 0x102c08 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x102c10 [0xBE, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102c10) (movR32Imm32Effect 0x102c10 5 6 0x20)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x102c10 5 6 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x102c10 0xbe (by decide) 0x20) pre_rip
  have f7 : InstrSpec 0x102c15 [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102c15) (movR32Imm32Effect 0x102c15 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x102c15 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x102c15 0xb9 (by decide) 0x4) pre_rip
  have f8 : InstrSpec 0x102c1a [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x102c1a) (movR64R64Effect 0x102c1a 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102c1a 7 14).toInstrSpec (mov_r64_r64_effect_step 0x102c1a 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x102c1d [0x41, 0xB8, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102c1d) (movR32Imm32Effect 0x102c1d 6 8 0x100)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x102c1d 6 8 0x100).toInstrSpec (mov_r32_imm32_rex_effect_step 0x102c1d 0x41 0xb8 (by decide) (by decide) 0x100) pre_rip
  have f10 : InstrSpec 0x102c23 [0xE8, 0x48, 0x51, 0x02, 0x00] (PushPre 0x102c23 5) (callEffect (fun _ => 0x127d70) 0x102c28)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102c23 0x127d70 0x102c28).toInstrSpec (call_rel32_effect_step 0x102c23 0x25148 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bd8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102be4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bf0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bfc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c08) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 58), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c10) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 58), (3, 3), (4, 4), (5, 5), (6, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c15) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 62), (2, 58), (3, 3), (4, 4), (5, 5), (6, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c1a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 62), (2, 58), (3, 3), (4, 4), (5, 5), (6, 60), (7, 64), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c1d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 62), (2, 58), (3, 3), (4, 4), (5, 5), (6, 60), (7, 64), (8, 66), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c23) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 62), (2, 58), (3, 3), (4, 68), (5, 5), (6, 60), (7, 64), (8, 66), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d70) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 70) (by decide) (by decide) rfl rfl

theorem block_l102bcd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102bcd :=
  Rest.liftedBlock (rest_l102bcd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102bcd x hx)

theorem rest_l102c28 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102c28 bytes_l102c28) (entryMap (live .l102c28))
      2 0x102c28 bytes_l102c28 b_l102c28 := by
  have f0 : InstrSpec 0x102c28 [0x3C, 0xFF] (fun s => s.RIP = 0x102c28) (cmpAlImm8Effect 0x102c28 0xff)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x102c28 0xff).toInstrSpec (cmp_al_imm8_effect_step 0x102c28 0xff) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c2a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x102c2a 5 0x330) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102c28 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102c28 :=
  Rest.liftedBlock (rest_l102c28 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102c28 x hx)

theorem rest_l102c30_1 [Bindings] (code : CodeMap) :
    Rest (n := 99) code lifted (codeRange 0x102c30 bytes_l102c30) [(0, 53), (1, 83), (2, 73), (3, 3), (4, 4), (5, 5), (6, 93), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 96), (22, 22), (39, 39), (50, 50), (51, 51)]
      3 0x102c95 bytes_l102c30_1 b_l102c30_1 := by
  have f20 : InstrSpec 0x102c95 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x102c95) (movR64R64Effect 0x102c95 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102c95 7 4).toInstrSpec (mov_r64_r64_effect_step 0x102c95 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x102c98 [0x80, 0x3C, 0x24, 0x00] (LoadPre 0x102c98 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102c98 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x102c98 4 (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x102c98 4 (.sib 4 none 0 .none) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x102c98 (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f20 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 53), (1, 83), (2, 73), (3, 3), (4, 4), (5, 5), (6, 93), (7, 99), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 96), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c98) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f21 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 53), (1, 83), (2, 73), (3, 3), (4, 4), (5, 5), (6, 93), (7, 99), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c9c) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 103) (jcc_rel32_effect_step 0x102c9c 4 0x1c0) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l102c30 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102c30 bytes_l102c30) (entryMap (live .l102c30))
      23 0x102c30 bytes_l102c30 b_l102c30 := by
  have f0 : InstrSpec 0x102c30 [0x48, 0x8B, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x102c30 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x102c30 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102c30 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102c30 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x102c30 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x102c38 [0x48, 0xB9, 0xBE, 0xBE, 0xC9, 0x2F, 0x73, 0xA1, 0x2D, 0x40] (fun s => s.RIP = 0x102c38) (movR64Imm64Effect 0x102c38 1 0x402da1732fc9bebe)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x102c38 1 0x402da1732fc9bebe).toInstrSpec (mov_r64_imm64_effect_step 0x102c38 0x48 0xb9 (by decide) (by decide) 0x402da1732fc9bebe) pre_rip
  have f2 : InstrSpec 0x102c42 [0x31, 0xF6] (fun s => s.RIP = 0x102c42) (xorR32R32Effect 0x102c42 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x102c42 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x102c42 0xf6 (by decide)) pre_rip
  have f3 : InstrSpec 0x102c44 [0x48, 0x39, 0xC8] (fun s => s.RIP = 0x102c44) (cmpR64R64Effect 0x102c44 0 1)
      [.gpr 0, .gpr 1] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x102c44 0 1).toInstrSpec (cmp_r64_r64_effect_step 0x102c44 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x102c47 [0x40, 0x0F, 0x97, 0xC6] (fun s => s.RIP = 0x102c47) (atFlags (condHolds 7) (setccR8Effect 0x102c47 4 6))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 6, .rip] :=
    (setccR8Effect_footprint 0x102c47 4 6 7).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x102c47 7 0x40 (by decide) 0xc6 (by decide) c)) pre_rip
  have f5 : InstrSpec 0x102c4b [0x31, 0xC9] (fun s => s.RIP = 0x102c4b) (xorR32R32Effect 0x102c4b 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x102c4b 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x102c4b 0xc9 (by decide)) pre_rip
  have f6 : InstrSpec 0x102c4d [0x48, 0x03, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x102c4d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x102c4d + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x102c4d 6 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (addR64M64Effect_footprint 0x102c4d 6 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (add_r64_m64_effect_step 0x102c4d 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x102c55 [0x0F, 0x92, 0xC1] (fun s => s.RIP = 0x102c55) (atFlags (condHolds 2) (setccR8Effect 0x102c55 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x102c55 3 1 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x102c55 2 0xc1 (by decide) (by decide) c)) pre_rip
  have f8 : InstrSpec 0x102c58 [0x48, 0xBA, 0x3B, 0xA0, 0x48, 0xAF, 0xE6, 0xDC, 0xAE, 0xBA] (fun s => s.RIP = 0x102c58) (movR64Imm64Effect 0x102c58 2 0xbaaedce6af48a03b)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x102c58 2 0xbaaedce6af48a03b).toInstrSpec (mov_r64_imm64_effect_step 0x102c58 0x48 0xba (by decide) (by decide) 0xbaaedce6af48a03b) pre_rip
  have f9 : InstrSpec 0x102c62 [0x48, 0x01, 0xF2] (fun s => s.RIP = 0x102c62) (addR64R64Effect 0x102c62 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x102c62 2 6).toInstrSpec (add_r64_r64_effect_step 0x102c62 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x102c65 [0x48, 0x13, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x102c65 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x102c65 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x102c65 1 (.sib 4 none 0 (.d32 0xc8))))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 1, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x102c65 1 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x102c65 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x102c6d [0x40, 0x0F, 0x92, 0xC6] (fun s => s.RIP = 0x102c6d) (atFlags (condHolds 2) (setccR8Effect 0x102c6d 4 6))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .rip] :=
    (setccR8Effect_footprint 0x102c6d 4 6 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x102c6d 2 0x40 (by decide) 0xc6 (by decide) c)) pre_rip
  have f12 : InstrSpec 0x102c71 [0x40, 0x0F, 0xB6, 0xF6] (fun s => s.RIP = 0x102c71) (movzxR32R8Effect 0x102c71 4 6 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (movzxR32R8Effect_footprint 0x102c71 4 6 6).toInstrSpec (movzx_r32_r8_rex_effect_step 0x102c71 0x40 (by decide) 0xf6 (by decide)) pre_rip
  have f13 : InstrSpec 0x102c75 [0x48, 0x83, 0xC1, 0xFE] (fun s => s.RIP = 0x102c75) (addR64Imm8Effect 0x102c75 1 0xfe)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x102c75 1 0xfe).toInstrSpec (add_r64_imm8_effect_step 0x102c75 0x48 0xc1 0xfe (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x102c79 [0x48, 0x13, 0xB4, 0x24, 0xD0, 0x00, 0x00, 0x00] (LoadPre 0x102c79 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x102c79 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x102c79 6 (.sib 4 none 0 (.d32 0xd0))))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x102c79 6 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x102c79 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x102c81 [0x40, 0x0F, 0x92, 0xC7] (fun s => s.RIP = 0x102c81) (atFlags (condHolds 2) (setccR8Effect 0x102c81 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x102c81 4 7 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x102c81 2 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f16 : InstrSpec 0x102c85 [0x40, 0x0F, 0xB6, 0xFF] (fun s => s.RIP = 0x102c85) (movzxR32R8Effect 0x102c85 4 7 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x102c85 4 7 7).toInstrSpec (movzx_r32_r8_rex_effect_step 0x102c85 0x40 (by decide) 0xff (by decide)) pre_rip
  have f17 : InstrSpec 0x102c89 [0x48, 0x83, 0xC6, 0xFF] (fun s => s.RIP = 0x102c89) (addR64Imm8Effect 0x102c89 6 0xff)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x102c89 6 0xff).toInstrSpec (add_r64_imm8_effect_step 0x102c89 0x48 0xc6 0xff (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x102c8d [0x48, 0x83, 0xD7, 0x00] (fun s => s.RIP = 0x102c8d) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x102c8d 7 0x0))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 7, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x102c8d 7 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x102c8d 0x48 0xd7 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f19 : InstrSpec 0x102c91 [0x0F, 0x94, 0x04, 0x24] (StorePre 0x102c91 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102c91 + BitVec.ofNat 64 4)) 1) (atFlags (condHolds 4) (setccM8Effect 0x102c91 4 (.sib 4 none 0 .none)))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x102c91 4 (.sib 4 none 0 .none) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x102c91 4 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c38) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c42) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c44) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c47) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c4b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 64), (3, 3), (4, 4), (5, 5), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c4d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f6 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 64), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c55) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 69), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c58) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 69), (2, 71), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c62) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f9 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 69), (2, 73), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c65) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 77) f10 .CF (fun _ => rfl) (adcR64M64Effect_fresh 0x102c65 1 (.sib 4 none 0 (.d32 0xc8)) _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 76), (2, 73), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c6d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 53), (1, 76), (2, 73), (3, 3), (4, 4), (5, 5), (6, 79), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c71) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 53), (1, 76), (2, 73), (3, 3), (4, 4), (5, 5), (6, 81), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c75) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 84) f13 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 85) (ρ' := [(0, 53), (1, 83), (2, 73), (3, 3), (4, 4), (5, 5), (6, 81), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c79) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 87) f14 .CF (fun _ => rfl) (adcR64M64Effect_fresh 0x102c79 6 (.sib 4 none 0 (.d32 0xd0)) _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 88) (ρ' := [(0, 53), (1, 83), (2, 73), (3, 3), (4, 4), (5, 5), (6, 86), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c81) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 53), (1, 83), (2, 73), (3, 3), (4, 4), (5, 5), (6, 86), (7, 89), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c85) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 53), (1, 83), (2, 73), (3, 3), (4, 4), (5, 5), (6, 86), (7, 91), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c89) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 94) f17 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 95) (ρ' := [(0, 53), (1, 83), (2, 73), (3, 3), (4, 4), (5, 5), (6, 93), (7, 91), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 94), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c8d) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.fresh (n := 96) f18 .ZF (fun _ => rfl) (adcR64Imm8Effect_fresh 0x102c8d 7 0x0 _ (.tail _ (.tail _ (.tail _ (.head _))))) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 53), (1, 83), (2, 73), (3, 3), (4, 4), (5, 5), (6, 93), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 96), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c91) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 53), (1, 83), (2, 73), (3, 3), (4, 4), (5, 5), (6, 93), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 96), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c95) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l102c30_1 code

theorem block_l102c30 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102c30 :=
  Rest.liftedBlock (rest_l102c30 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102c30 x hx)

theorem rest_l102ca2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102ca2 bytes_l102ca2) (entryMap (live .l102ca2))
      10 0x102ca2 bytes_l102ca2 b_l102ca2 := by
  have f0 : InstrSpec 0x102ca2 [0x48, 0xBF, 0x41, 0x41, 0x36, 0xD0, 0x8C, 0x5E, 0xD2, 0xBF] (fun s => s.RIP = 0x102ca2) (movR64Imm64Effect 0x102ca2 7 0xbfd25e8cd0364141)
      [] [] [.reg 7, .rip] :=
    (movR64Imm64Effect_footprint 0x102ca2 7 0xbfd25e8cd0364141).toInstrSpec (mov_r64_imm64_effect_step 0x102ca2 0x48 0xbf (by decide) (by decide) 0xbfd25e8cd0364141) pre_rip
  have f1 : InstrSpec 0x102cac [0x48, 0x01, 0xF8] (fun s => s.RIP = 0x102cac) (addR64R64Effect 0x102cac 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x102cac 0 7).toInstrSpec (add_r64_r64_effect_step 0x102cac 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102caf [0x48, 0x0F, 0xCE] (fun s => s.RIP = 0x102caf) (bswapR64Effect 0x102caf 3 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (bswapR64Effect_footprint 0x102caf 3 6).toInstrSpec (bswap_r64_effect_step 0x102caf 0x48 (by decide) 0xce (by decide)) pre_rip
  have f3 : InstrSpec 0x102cb2 [0x48, 0x0F, 0xC9] (fun s => s.RIP = 0x102cb2) (bswapR64Effect 0x102cb2 3 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR64Effect_footprint 0x102cb2 3 1).toInstrSpec (bswap_r64_effect_step 0x102cb2 0x48 (by decide) 0xc9 (by decide)) pre_rip
  have f4 : InstrSpec 0x102cb5 [0x48, 0x0F, 0xCA] (fun s => s.RIP = 0x102cb5) (bswapR64Effect 0x102cb5 3 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR64Effect_footprint 0x102cb5 3 2).toInstrSpec (bswap_r64_effect_step 0x102cb5 0x48 (by decide) 0xca (by decide)) pre_rip
  have f5 : InstrSpec 0x102cb8 [0x48, 0x0F, 0xC8] (fun s => s.RIP = 0x102cb8) (bswapR64Effect 0x102cb8 3 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (bswapR64Effect_footprint 0x102cb8 3 0).toInstrSpec (bswap_r64_effect_step 0x102cb8 0x48 (by decide) 0xc8 (by decide)) pre_rip
  have f6 : InstrSpec 0x102cbb [0x48, 0x89, 0xB4, 0x24, 0x50, 0x01, 0x00, 0x00] (StorePre 0x102cbb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x102cbb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102cbb 6 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102cbb 6 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (mov_m64_r64_effect_step 0x102cbb 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x102cc3 [0x48, 0x89, 0x8C, 0x24, 0x58, 0x01, 0x00, 0x00] (StorePre 0x102cc3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x102cc3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102cc3 1 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102cc3 1 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (mov_m64_r64_effect_step 0x102cc3 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x102ccb [0x48, 0x89, 0x94, 0x24, 0x60, 0x01, 0x00, 0x00] (StorePre 0x102ccb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x102ccb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102ccb 2 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102ccb 2 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (mov_m64_r64_effect_step 0x102ccb 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x102cd3 [0x48, 0x89, 0x84, 0x24, 0x68, 0x01, 0x00, 0x00] (StorePre 0x102cd3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x102cd3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102cd3 0 (.sib 4 none 0 (.d32 0x168)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102cd3 0 (.sib 4 none 0 (.d32 0x168))).toInstrSpec (mov_m64_r64_effect_step 0x102cd3 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x168)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cac) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102caf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cb2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cb5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cb8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cbb) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cc3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 63), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ccb) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 63), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cd3) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 63), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cdb) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 69) (by decide) rfl

theorem block_l102ca2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102ca2 :=
  Rest.liftedBlock (rest_l102ca2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102ca2 x hx)

theorem rest_l102cdb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102cdb bytes_l102cdb) (entryMap (live .l102cdb))
      3 0x102cdb bytes_l102cdb b_l102cdb := by
  have f0 : InstrSpec 0x102cdb [0x40, 0x80, 0xE5, 0x01] (fun s => s.RIP = 0x102cdb) (andR8Imm8Effect 0x102cdb 4 5 0x1)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x102cdb 4 5 0x1).toInstrSpec (and_r8_imm8_rex_effect_step 0x102cdb 0x40 0xe5 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102cdf [0x40, 0x0F, 0xB6, 0xFD] (fun s => s.RIP = 0x102cdf) (movzxR32R8Effect 0x102cdf 4 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x102cdf 4 7 5).toInstrSpec (movzx_r32_r8_rex_effect_step 0x102cdf 0x40 (by decide) 0xfd (by decide)) pre_rip
  have f2 : InstrSpec 0x102ce3 [0xE8, 0x68, 0x50, 0x02, 0x00] (PushPre 0x102ce3 5) (callEffect (fun _ => 0x127d50) 0x102ce8)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102ce3 0x127d50 0x102ce8).toInstrSpec (call_rel32_effect_step 0x102ce3 0x25068 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cdf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ce3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 53), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l102cdb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102cdb :=
  Rest.liftedBlock (rest_l102cdb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102cdb x hx)

theorem rest_l102ce8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102ce8 bytes_l102ce8) (entryMap (live .l102ce8))
      4 0x102ce8 bytes_l102ce8 b_l102ce8 := by
  have f0 : InstrSpec 0x102ce8 [0x0F, 0xB6, 0xD0] (fun s => s.RIP = 0x102ce8) (movzxR32R8Effect 0x102ce8 3 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x102ce8 3 2 0).toInstrSpec (movzx_r32_r8_effect_step 0x102ce8 0xd0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102ceb [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x102ceb) (movR64R64Effect 0x102ceb 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102ceb 7 4).toInstrSpec (mov_r64_r64_effect_step 0x102ceb 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102cee [0x48, 0x8D, 0xB4, 0x24, 0x50, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102cee) (leaR64Effect 0x102cee 6 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102cee 6 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (lea_r64_effect_step 0x102cee 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102cf6 [0xE8, 0xB5, 0xD8, 0x01, 0x00] (PushPre 0x102cf6 5) (callEffect (fun _ => 0x1205b0) 0x102cfb)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102cf6 0x1205b0 0x102cfb).toInstrSpec (call_rel32_effect_step 0x102cf6 0x1d8b5 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ceb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cee) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cf6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205b0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l102ce8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102ce8 :=
  Rest.liftedBlock (rest_l102ce8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102ce8 x hx)

theorem rest_l102cfb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102cfb bytes_l102cfb) (entryMap (live .l102cfb))
      2 0x102cfb bytes_l102cfb b_l102cfb := by
  have f0 : InstrSpec 0x102cfb [0x80, 0x7C, 0x24, 0x58, 0x01] (LoadPre 0x102cfb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x102cfb + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x102cfb 5 (.sib 4 none 0 (.d8 0x58)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x102cfb 5 (.sib 4 none 0 (.d8 0x58)) 0x1).toInstrSpec (cmp_m8_imm8_effect_step 0x102cfb (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d00) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x102d00 5 0x15c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102cfb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102cfb :=
  Rest.liftedBlock (rest_l102cfb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102cfb x hx)

theorem rest_l102d06 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102d06 bytes_l102d06) (entryMap (live .l102d06))
      11 0x102d06 bytes_l102d06 b_l102d06 := by
  have f0 : InstrSpec 0x102d06 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x102d06) (leaR64Effect 0x102d06 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102d06 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x102d06 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102d0b [0x48, 0x8B, 0x04, 0x24] (LoadPre 0x102d0b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102d0b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102d0b 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102d0b 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x102d0b 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x102d0f [0x48, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x102d0f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x102d0f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102d0f 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x102d0f 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x102d0f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x102d14 [0x48, 0x8D, 0xBC, 0x24, 0x58, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x102d14) (leaR64Effect 0x102d14 7 (.sib 4 none 0 (.d32 0x258)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102d14 7 (.sib 4 none 0 (.d32 0x258))).toInstrSpec (lea_r64_effect_step 0x102d14 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x258)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x102d1c [0xB9, 0x09, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102d1c) (movR32Imm32Effect 0x102d1c 5 1 0x9)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x102d1c 5 1 0x9).toInstrSpec (mov_r32_imm32_effect_step 0x102d1c 0xb9 (by decide) 0x9) pre_rip
  have f5 : InstrSpec 0x102d21 [0xF3, 0x48, 0xA5] (RepPre 0x102d21 (RepMovsqPre 0x102d21)) (repMovsqEffect 0x102d21)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x102d21).toInstrSpecOfRuns (rep_movsq_runs hstride 0x102d21 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f6 : InstrSpec 0x102d24 [0x48, 0x89, 0x84, 0x24, 0x48, 0x02, 0x00, 0x00] (StorePre 0x102d24 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x248)) s (0x102d24 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102d24 0 (.sib 4 none 0 (.d32 0x248)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102d24 0 (.sib 4 none 0 (.d32 0x248))).toInstrSpec (mov_m64_r64_effect_step 0x102d24 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x248)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x102d2c [0x48, 0x89, 0x94, 0x24, 0x50, 0x02, 0x00, 0x00] (StorePre 0x102d2c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x250)) s (0x102d2c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102d2c 2 (.sib 4 none 0 (.d32 0x250)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102d2c 2 (.sib 4 none 0 (.d32 0x250))).toInstrSpec (mov_m64_r64_effect_step 0x102d2c 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x250)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x102d34 [0x48, 0x8D, 0xBC, 0x24, 0xD0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102d34) (leaR64Effect 0x102d34 7 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102d34 7 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (lea_r64_effect_step 0x102d34 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x102d3c [0x48, 0x8D, 0xB4, 0x24, 0x48, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x102d3c) (leaR64Effect 0x102d3c 6 (.sib 4 none 0 (.d32 0x248)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102d3c 6 (.sib 4 none 0 (.d32 0x248))).toInstrSpec (lea_r64_effect_step 0x102d3c 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x248)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x102d44 [0xE8, 0xC7, 0xCC, 0x00, 0x00] (PushPre 0x102d44 5) (callEffect (fun _ => 0x10fa10) 0x102d49)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102d44 0x10fa10 0x102d49).toInstrSpec (call_rel32_effect_step 0x102d44 0xccc7 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d0b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d0f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d14) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d1c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d21) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 63), (2, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d24) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 55), (1, 63), (2, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d2c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 63), (2, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d34) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 63), (2, 57), (3, 3), (4, 4), (5, 5), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d3c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 63), (2, 57), (3, 3), (4, 4), (5, 5), (6, 69), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d44) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 63), (2, 57), (3, 3), (4, 71), (5, 5), (6, 69), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa10) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l102d06 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102d06 :=
  Rest.liftedBlock (rest_l102d06 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102d06 x hx)

theorem rest_l102d49 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102d49 bytes_l102d49) (entryMap (live .l102d49))
      3 0x102d49 bytes_l102d49 b_l102d49 := by
  have f0 : InstrSpec 0x102d49 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x102d49) (movR64R64Effect 0x102d49 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102d49 7 4).toInstrSpec (mov_r64_r64_effect_step 0x102d49 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102d4c [0x48, 0x8D, 0xB4, 0x24, 0x30, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102d4c) (leaR64Effect 0x102d4c 6 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102d4c 6 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (lea_r64_effect_step 0x102d4c 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102d54 [0xE8, 0x27, 0x70, 0x00, 0x00] (PushPre 0x102d54 5) (callEffect (fun _ => 0x109d80) 0x102d59)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102d54 0x109d80 0x102d59).toInstrSpec (call_rel32_effect_step 0x102d54 0x7027 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d4c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d54) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d80) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l102d49 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102d49 :=
  Rest.liftedBlock (rest_l102d49 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102d49 x hx)

theorem rest_l102d59 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102d59 bytes_l102d59) (entryMap (live .l102d59))
      4 0x102d59 bytes_l102d59 b_l102d59 := by
  have f0 : InstrSpec 0x102d59 [0x0F, 0xB6, 0x44, 0x24, 0x20] (LoadPre 0x102d59 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x102d59 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102d59 5 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x102d59 5 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (movzx_r32_m8_effect_step 0x102d59 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x102d5e [0x88, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x102d5e 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x102d5e + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x102d5e 7 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x102d5e 7 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m8_r8_effect_step 0x102d5e 0 (by decide) (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x102d65 [0x3C, 0x01] (fun s => s.RIP = 0x102d65) (cmpAlImm8Effect 0x102d65 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x102d65 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x102d65 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d5e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d65) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (12, 12), (13, 13), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d67) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel32_effect_step 0x102d67 5 0x230) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102d59 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102d59 :=
  Rest.liftedBlock (rest_l102d59 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102d59 x hx)

theorem rest_l102d6d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102d6d bytes_l102d6d) (entryMap (live .l102d6d))
      17 0x102d6d bytes_l102d6d b_l102d6d := by
  have f0 : InstrSpec 0x102d6d [0x48, 0x8B, 0x04, 0x24] (LoadPre 0x102d6d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102d6d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102d6d 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102d6d 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x102d6d 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x102d71 [0x48, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x102d71 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x102d71 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102d71 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x102d71 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x102d71 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x102d76 [0x48, 0x89, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00] (StorePre 0x102d76 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x102d76 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102d76 0 (.sib 4 none 0 (.d32 0x170)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102d76 0 (.sib 4 none 0 (.d32 0x170))).toInstrSpec (mov_m64_r64_effect_step 0x102d76 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x102d7e [0x48, 0x89, 0x8C, 0x24, 0x78, 0x01, 0x00, 0x00] (StorePre 0x102d7e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x102d7e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102d7e 1 (.sib 4 none 0 (.d32 0x178)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102d7e 1 (.sib 4 none 0 (.d32 0x178))).toInstrSpec (mov_m64_r64_effect_step 0x102d7e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x178)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x102d86 [0x48, 0x8B, 0x54, 0x24, 0x10] (LoadPre 0x102d86 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102d86 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102d86 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x102d86 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x102d86 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x102d8b [0x48, 0x89, 0x94, 0x24, 0x80, 0x01, 0x00, 0x00] (StorePre 0x102d8b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x102d8b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102d8b 2 (.sib 4 none 0 (.d32 0x180)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102d8b 2 (.sib 4 none 0 (.d32 0x180))).toInstrSpec (mov_m64_r64_effect_step 0x102d8b 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x180)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x102d93 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x102d93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102d93 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102d93 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x102d93 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x102d93 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x102d98 [0x48, 0x89, 0xB4, 0x24, 0x88, 0x01, 0x00, 0x00] (StorePre 0x102d98 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x102d98 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102d98 6 (.sib 4 none 0 (.d32 0x188)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102d98 6 (.sib 4 none 0 (.d32 0x188))).toInstrSpec (mov_m64_r64_effect_step 0x102d98 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x188)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x102da0 [0x48, 0x89, 0x74, 0x24, 0x18] (StorePre 0x102da0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102da0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102da0 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102da0 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x102da0 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x102da5 [0x48, 0x89, 0x54, 0x24, 0x10] (StorePre 0x102da5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102da5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102da5 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102da5 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x102da5 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x102daa [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x102daa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x102daa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102daa 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102daa 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x102daa 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x102daf [0x48, 0x89, 0x04, 0x24] (StorePre 0x102daf 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102daf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102daf 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102daf 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x102daf 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x102db3 [0x4C, 0x8D, 0xB4, 0x24, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102db3) (leaR64Effect 0x102db3 14 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x102db3 14 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (lea_r64_effect_step 0x102db3 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x102dbb [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x102dbb) (movR64R64Effect 0x102dbb 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102dbb 6 4).toInstrSpec (mov_r64_r64_effect_step 0x102dbb 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x102dbe [0x48, 0x8D, 0x94, 0x24, 0xB0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102dbe) (leaR64Effect 0x102dbe 2 (.sib 4 none 0 (.d32 0x1b0)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x102dbe 2 (.sib 4 none 0 (.d32 0x1b0))).toInstrSpec (lea_r64_effect_step 0x102dbe 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x1b0)) (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x102dc6 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x102dc6) (movR64R64Effect 0x102dc6 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102dc6 7 14).toInstrSpec (mov_r64_r64_effect_step 0x102dc6 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x102dc9 [0xE8, 0x92, 0x71, 0x00, 0x00] (PushPre 0x102dc9 5) (callEffect (fun _ => 0x109f60) 0x102dce)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102dc9 0x109f60 0x102dce).toInstrSpec (call_rel32_effect_step 0x102dc9 0x7192 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d71) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d76) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d7e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d86) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d8b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d93) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d98) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102da0) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102da5) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102daa) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102daf) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102db3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dbb) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 71), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dbe) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 55), (2, 73), (3, 3), (4, 4), (5, 5), (6, 71), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dc6) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 53), (1, 55), (2, 73), (3, 3), (4, 4), (5, 5), (6, 71), (7, 75), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dc9) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 55), (2, 73), (3, 3), (4, 77), (5, 5), (6, 71), (7, 75), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f60) f16 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 79) (by decide) (by decide) rfl rfl

theorem block_l102d6d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102d6d :=
  Rest.liftedBlock (rest_l102d6d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102d6d x hx)

theorem rest_l102dce [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102dce bytes_l102dce) (entryMap (live .l102dce))
      4 0x102dce bytes_l102dce b_l102dce := by
  have f0 : InstrSpec 0x102dce [0x4C, 0x8D, 0xBC, 0x24, 0x50, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x102dce) (leaR64Effect 0x102dce 15 (.sib 4 none 0 (.d32 0x350)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x102dce 15 (.sib 4 none 0 (.d32 0x350))).toInstrSpec (lea_r64_effect_step 0x102dce 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x350)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102dd6 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x102dd6) (movR64R64Effect 0x102dd6 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102dd6 7 15).toInstrSpec (mov_r64_r64_effect_step 0x102dd6 0x4c 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102dd9 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x102dd9) (movR64R64Effect 0x102dd9 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102dd9 6 14).toInstrSpec (mov_r64_r64_effect_step 0x102dd9 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102ddc [0xE8, 0xEF, 0x74, 0x00, 0x00] (PushPre 0x102ddc 5) (callEffect (fun _ => 0x10a2d0) 0x102de1)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102ddc 0x10a2d0 0x102de1).toInstrSpec (call_rel32_effect_step 0x102ddc 0x74ef (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dd6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dd9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ddc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2d0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l102dce [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102dce :=
  Rest.liftedBlock (rest_l102dce code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102dce x hx)

theorem rest_l102de1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102de1 bytes_l102de1) (entryMap (live .l102de1))
      5 0x102de1 bytes_l102de1 b_l102de1 := by
  have f0 : InstrSpec 0x102de1 [0x4C, 0x8D, 0xB4, 0x24, 0x70, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x102de1) (leaR64Effect 0x102de1 14 (.sib 4 none 0 (.d32 0x370)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x102de1 14 (.sib 4 none 0 (.d32 0x370))).toInstrSpec (lea_r64_effect_step 0x102de1 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x370)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102de9 [0x48, 0x8D, 0xB4, 0x24, 0x70, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102de9) (leaR64Effect 0x102de9 6 (.sib 4 none 0 (.d32 0x170)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102de9 6 (.sib 4 none 0 (.d32 0x170))).toInstrSpec (lea_r64_effect_step 0x102de9 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102df1 [0x48, 0x8D, 0x94, 0x24, 0x90, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102df1) (leaR64Effect 0x102df1 2 (.sib 4 none 0 (.d32 0x190)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x102df1 2 (.sib 4 none 0 (.d32 0x190))).toInstrSpec (lea_r64_effect_step 0x102df1 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x190)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102df9 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x102df9) (movR64R64Effect 0x102df9 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102df9 7 14).toInstrSpec (mov_r64_r64_effect_step 0x102df9 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x102dfc [0xE8, 0x5F, 0x71, 0x00, 0x00] (PushPre 0x102dfc 5) (callEffect (fun _ => 0x109f60) 0x102e01)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102dfc 0x109f60 0x102e01).toInstrSpec (call_rel32_effect_step 0x102dfc 0x715f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102de9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102df1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102df9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dfc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 57), (3, 3), (4, 61), (5, 5), (6, 55), (7, 59), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f60) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l102de1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102de1 :=
  Rest.liftedBlock (rest_l102de1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102de1 x hx)

theorem rest_l102e01 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102e01 bytes_l102e01) (entryMap (live .l102e01))
      6 0x102e01 bytes_l102e01 b_l102e01 := by
  have f0 : InstrSpec 0x102e01 [0x4C, 0x8D, 0xA4, 0x24, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102e01) (leaR64Effect 0x102e01 12 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x102e01 12 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (lea_r64_effect_step 0x102e01 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102e09 [0x48, 0x8D, 0x8C, 0x24, 0xD0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102e09) (leaR64Effect 0x102e09 1 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x102e09 1 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (lea_r64_effect_step 0x102e09 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102e11 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x102e11) (movR64R64Effect 0x102e11 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102e11 7 12).toInstrSpec (mov_r64_r64_effect_step 0x102e11 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102e14 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x102e14) (movR64R64Effect 0x102e14 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102e14 6 15).toInstrSpec (mov_r64_r64_effect_step 0x102e14 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x102e17 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x102e17) (movR64R64Effect 0x102e17 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x102e17 2 14).toInstrSpec (mov_r64_r64_effect_step 0x102e17 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x102e1a [0xE8, 0x01, 0xCD, 0x00, 0x00] (PushPre 0x102e1a 5) (callEffect (fun _ => 0x10fb20) 0x102e1f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102e1a 0x10fb20 0x102e1f).toInstrSpec (call_rel32_effect_step 0x102e1a 0xcd01 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e09) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e11) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (7, 57), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e14) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e17) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e1a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 55), (2, 61), (3, 3), (4, 63), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb20) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l102e01 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102e01 :=
  Rest.liftedBlock (rest_l102e01 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102e01 x hx)

theorem rest_l102e1f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102e1f bytes_l102e1f) (entryMap (live .l102e1f))
      4 0x102e1f bytes_l102e1f b_l102e1f := by
  have f0 : InstrSpec 0x102e1f [0x4C, 0x8D, 0xB4, 0x24, 0xA0, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x102e1f) (leaR64Effect 0x102e1f 14 (.sib 4 none 0 (.d32 0x2a0)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x102e1f 14 (.sib 4 none 0 (.d32 0x2a0))).toInstrSpec (lea_r64_effect_step 0x102e1f 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x2a0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102e27 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x102e27) (movR64R64Effect 0x102e27 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102e27 7 14).toInstrSpec (mov_r64_r64_effect_step 0x102e27 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102e2a [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x102e2a) (movR64R64Effect 0x102e2a 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102e2a 6 12).toInstrSpec (mov_r64_r64_effect_step 0x102e2a 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102e2d [0xE8, 0x1E, 0xD0, 0x00, 0x00] (PushPre 0x102e2d 5) (callEffect (fun _ => 0x10fe50) 0x102e32)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102e2d 0x10fe50 0x102e32).toInstrSpec (call_rel32_effect_step 0x102e2d 0xd01e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e27) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e2a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e2d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l102e1f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102e1f :=
  Rest.liftedBlock (rest_l102e1f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102e1f x hx)

theorem rest_l102e32 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102e32 bytes_l102e32) (entryMap (live .l102e32))
      9 0x102e32 bytes_l102e32 b_l102e32 := by
  have f0 : InstrSpec 0x102e32 [0x48, 0x8D, 0x84, 0x24, 0xF8, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x102e32) (leaR64Effect 0x102e32 0 (.sib 4 none 0 (.d32 0x2f8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x102e32 0 (.sib 4 none 0 (.d32 0x2f8))).toInstrSpec (lea_r64_effect_step 0x102e32 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x2f8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102e3a [0xB9, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102e3a) (movR32Imm32Effect 0x102e3a 5 1 0xb)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x102e3a 5 1 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x102e3a 0xb9 (by decide) 0xb) pre_rip
  have f2 : InstrSpec 0x102e3f [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x102e3f) (movR64R64Effect 0x102e3f 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102e3f 7 0).toInstrSpec (mov_r64_r64_effect_step 0x102e3f 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102e42 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x102e42) (movR64R64Effect 0x102e42 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102e42 6 14).toInstrSpec (mov_r64_r64_effect_step 0x102e42 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x102e45 [0xF3, 0x48, 0xA5] (RepPre 0x102e45 (RepMovsqPre 0x102e45)) (repMovsqEffect 0x102e45)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x102e45).toInstrSpecOfRuns (rep_movsq_runs hstride 0x102e45 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x102e48 [0x49, 0x89, 0xE6] (fun s => s.RIP = 0x102e48) (movR64R64Effect 0x102e48 14 4)
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x102e48 14 4).toInstrSpec (mov_r64_r64_effect_step 0x102e48 0x49 0xe6 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x102e4b [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x102e4b) (movR64R64Effect 0x102e4b 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102e4b 7 14).toInstrSpec (mov_r64_r64_effect_step 0x102e4b 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x102e4e [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x102e4e) (movR64R64Effect 0x102e4e 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102e4e 6 0).toInstrSpec (mov_r64_r64_effect_step 0x102e4e 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x102e51 [0xE8, 0xBA, 0xCB, 0x00, 0x00] (PushPre 0x102e51 5) (callEffect (fun _ => 0x10fa10) 0x102e56)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102e51 0x10fa10 0x102e56).toInstrSpec (call_rel32_effect_step 0x102e51 0xcbba (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e3a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e3f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e42) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e45) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e48) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e4b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e4e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e51) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa10) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l102e32 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102e32 :=
  Rest.liftedBlock (rest_l102e32 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102e32 x hx)

theorem rest_l102e56 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102e56 bytes_l102e56) (entryMap (live .l102e56))
      2 0x102e56 bytes_l102e56 b_l102e56 := by
  have f0 : InstrSpec 0x102e56 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x102e56) (movR64R64Effect 0x102e56 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102e56 7 14).toInstrSpec (mov_r64_r64_effect_step 0x102e56 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102e59 [0xE8, 0x02, 0xD0, 0x00, 0x00] (PushPre 0x102e59 5) (callEffect (fun _ => 0x10fe60) 0x102e5e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102e59 0x10fe60 0x102e5e).toInstrSpec (call_rel32_effect_step 0x102e59 0xd002 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e59) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe60) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l102e56 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102e56 :=
  Rest.liftedBlock (rest_l102e56 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102e56 x hx)

theorem rest_l102e5e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102e5e bytes_l102e5e) (entryMap (live .l102e5e))
      2 0x102e5e bytes_l102e5e b_l102e5e := by
  have f0 : InstrSpec 0x102e5e [0x84, 0xC0] (fun s => s.RIP = 0x102e5e) (testR8R8Effect 0x102e5e 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x102e5e 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x102e5e 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e60) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x102e60 4 0x15) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102e5e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102e5e :=
  Rest.liftedBlock (rest_l102e5e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102e5e x hx)

theorem rest_l102e62 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102e62 bytes_l102e62) (entryMap (live .l102e62))
      1 0x102e62 bytes_l102e62 b_l102e62 := by
  have f0 : InstrSpec 0x102e62 [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102e62) (movR32Imm32Effect 0x102e62 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x102e62 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x102e62 0xb8 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e67) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l102e62 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102e62 :=
  Rest.liftedBlock (rest_l102e62 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102e62 x hx)

theorem rest_l102e67 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102e67 bytes_l102e67) (entryMap (live .l102e67))
      7 0x102e67 bytes_l102e67 b_l102e67 := by
  have f0 : InstrSpec 0x102e67 [0x48, 0x81, 0xC4, 0x90, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x102e67) (addR64Imm32Effect 0x102e67 4 0x390)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x102e67 4 0x390).toInstrSpec (add_r64_imm32_effect_step 0x102e67 0x48 0xc4 0x390 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102e6e [0x5B] (PopPre 0x102e6e) (popR64Effect 0x102e6e 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102e6e 1 3).toInstrSpec (pop_r64_effect_step 0x102e6e 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x102e6f [0x41, 0x5C] (PopPre 0x102e6f) (popR64Effect 0x102e6f 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102e6f 2 12).toInstrSpec (pop_r64_rex_effect_step 0x102e6f 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x102e71 [0x41, 0x5E] (PopPre 0x102e71) (popR64Effect 0x102e71 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102e71 2 14).toInstrSpec (pop_r64_rex_effect_step 0x102e71 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x102e73 [0x41, 0x5F] (PopPre 0x102e73) (popR64Effect 0x102e73 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102e73 2 15).toInstrSpec (pop_r64_rex_effect_step 0x102e73 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x102e75 [0x5D] (PopPre 0x102e75) (popR64Effect 0x102e75 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102e75 1 5).toInstrSpec (pop_r64_effect_step 0x102e75 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x102e76 [0xC3] (RetPre 0x102e76) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x102e76).toInstrSpec (ret_effect_step 0x102e76) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e6e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e6f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e71) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e73) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (14, 61), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e75) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (14, 61), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e76) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (14, 61), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) f6 (by decide) rfl rfl rfl (by decide)

theorem block_l102e67 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102e67 :=
  Rest.liftedBlock (rest_l102e67 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102e67 x hx)

theorem rest_l102e77 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102e77 bytes_l102e77) (entryMap (live .l102e77))
      13 0x102e77 bytes_l102e77 b_l102e77 := by
  have f0 : InstrSpec 0x102e77 [0x48, 0x8B, 0x84, 0x24, 0xA0, 0x02, 0x00, 0x00] (LoadPre 0x102e77 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2a0)) s (0x102e77 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102e77 0 (.sib 4 none 0 (.d32 0x2a0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x102e77 0 (.sib 4 none 0 (.d32 0x2a0))).toInstrSpec (mov_r64_m64_effect_step 0x102e77 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x2a0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x102e7f [0x48, 0x8B, 0x94, 0x24, 0xA8, 0x02, 0x00, 0x00] (LoadPre 0x102e7f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2a8)) s (0x102e7f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102e7f 2 (.sib 4 none 0 (.d32 0x2a8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x102e7f 2 (.sib 4 none 0 (.d32 0x2a8))).toInstrSpec (mov_r64_m64_effect_step 0x102e7f 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x2a8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x102e87 [0x48, 0x8D, 0xB4, 0x24, 0xB0, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x102e87) (leaR64Effect 0x102e87 6 (.sib 4 none 0 (.d32 0x2b0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102e87 6 (.sib 4 none 0 (.d32 0x2b0))).toInstrSpec (lea_r64_effect_step 0x102e87 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x2b0)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102e8f [0x48, 0x8D, 0x7C, 0x24, 0x18] (fun s => s.RIP = 0x102e8f) (leaR64Effect 0x102e8f 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102e8f 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (lea_r64_effect_step 0x102e8f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x102e94 [0xB9, 0x09, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102e94) (movR32Imm32Effect 0x102e94 5 1 0x9)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x102e94 5 1 0x9).toInstrSpec (mov_r32_imm32_effect_step 0x102e94 0xb9 (by decide) 0x9) pre_rip
  have f5 : InstrSpec 0x102e99 [0xF3, 0x48, 0xA5] (RepPre 0x102e99 (RepMovsqPre 0x102e99)) (repMovsqEffect 0x102e99)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x102e99).toInstrSpecOfRuns (rep_movsq_runs hstride 0x102e99 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f6 : InstrSpec 0x102e9c [0x48, 0x89, 0x54, 0x24, 0x10] (StorePre 0x102e9c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102e9c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102e9c 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102e9c 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x102e9c 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x102ea1 [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x102ea1) (leaR64Effect 0x102ea1 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102ea1 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x102ea1 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x102ea6 [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x102ea6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x102ea6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102ea6 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102ea6 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x102ea6 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x102eab [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102eab 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102eab + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x102eab (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102eab (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102eab 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x102eb3 [0x48, 0x8D, 0xBC, 0x24, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102eb3) (leaR64Effect 0x102eb3 7 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102eb3 7 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (lea_r64_effect_step 0x102eb3 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x102ebb [0x31, 0xD2] (fun s => s.RIP = 0x102ebb) (xorR32R32Effect 0x102ebb 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x102ebb 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x102ebb 0xd2 (by decide)) pre_rip
  have f12 : InstrSpec 0x102ebd [0xE8, 0x1E, 0xE7, 0x01, 0x00] (PushPre 0x102ebd 5) (callEffect (fun _ => 0x1215e0) 0x102ec2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102ebd 0x1215e0 0x102ec2).toInstrSpec (call_rel32_effect_step 0x102ebd 0x1e71e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e7f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e87) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e8f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e94) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e99) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e9c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ea1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 65), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ea6) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 65), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102eab) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 65), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102eb3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 65), (7, 69), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ebb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (2, 71), (3, 3), (4, 4), (5, 5), (6, 65), (7, 69), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ebd) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (2, 71), (3, 3), (4, 73), (5, 5), (6, 65), (7, 69), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215e0) f12 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l102e77 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102e77 :=
  Rest.liftedBlock (rest_l102e77 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102e77 x hx)

theorem rest_l102ec2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102ec2 bytes_l102ec2) (entryMap (live .l102ec2))
      7 0x102ec2 bytes_l102ec2 b_l102ec2 := by
  have f0 : InstrSpec 0x102ec2 [0x0F, 0xB6, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x102ec2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x102ec2 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x102ec2 8 1 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x102ec2 8 1 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (movzx_r32_m8_effect_step 0x102ec2 1 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x102eca [0x48, 0x83, 0xF9, 0x06] (fun s => s.RIP = 0x102eca) (cmpR64Imm8Effect 0x102eca 1 0x6)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x102eca 1 0x6).toInstrSpec (cmp_r64_imm8_effect_step 0x102eca 0x48 0xf9 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102ece [0x0F, 0x92, 0xC0] (fun s => s.RIP = 0x102ece) (atFlags (condHolds 2) (setccR8Effect 0x102ece 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x102ece 3 0 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x102ece 2 0xc0 (by decide) (by decide) c)) pre_rip
  have f3 : InstrSpec 0x102ed1 [0xB2, 0x3D] (fun s => s.RIP = 0x102ed1) (movR8Imm8Effect 0x102ed1 2 2 0x3d)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR8Imm8Effect_footprint 0x102ed1 2 2 0x3d).toInstrSpec (mov_r8_imm8_effect_step 0x102ed1 0xb2 (by decide) 0x3d) pre_rip
  have f4 : InstrSpec 0x102ed3 [0xD2, 0xEA] (fun s => s.RIP = 0x102ed3) (shrR8ClEffect 0x102ed3 2 2)
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR8ClEffect_footprint 0x102ed3 2 2).toInstrSpec (shr_r8_cl_effect_step 0x102ed3 0xea (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x102ed5 [0x84, 0xD0] (fun s => s.RIP = 0x102ed5) (testR8R8Effect 0x102ed5 2 0 2)
      [.gpr 0, .gpr 2] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x102ed5 2 0 2).toInstrSpec (test_r8_r8_effect_step 0x102ed5 0xd0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102eca) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ece) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ed1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 53), (2, 59), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ed3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 53), (2, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ed5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 53), (2, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ed7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 65) (jcc_rel8_effect_step 0x102ed7 5 0x32) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102ec2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102ec2 :=
  Rest.liftedBlock (rest_l102ec2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102ec2 x hx)

theorem rest_l102ed9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102ed9 bytes_l102ed9) (entryMap (live .l102ed9))
      7 0x102ed9 bytes_l102ed9 b_l102ed9 := by
  have f0 : InstrSpec 0x102ed9 [0xC7, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00] (StorePre 0x102ed9 11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x102ed9 + BitVec.ofNat 64 11)) 4) (movM32Imm32Effect 0x102ed9 11 (.sib 4 none 0 (.d32 0x1d0)) 0x3)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x102ed9 11 (.sib 4 none 0 (.d32 0x1d0)) 0x3).toInstrSpec (mov_m32_imm32_effect_step 0x102ed9 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide) 0x3) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x102ee4 [0x48, 0x8D, 0x94, 0x24, 0xD0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102ee4) (leaR64Effect 0x102ee4 2 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x102ee4 2 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (lea_r64_effect_step 0x102ee4 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102eec [0xBE, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102eec) (movR32Imm32Effect 0x102eec 5 6 0xb)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x102eec 5 6 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x102eec 0xbe (by decide) 0xb) pre_rip
  have f3 : InstrSpec 0x102ef1 [0x48, 0xC7, 0xC7, 0x00, 0x28, 0x20, 0x00] (fun s => s.RIP = 0x102ef1) (movR64Imm32Effect 0x102ef1 7 0x202800)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x102ef1 7 0x202800).toInstrSpec (mov_r64_imm32_effect_step 0x102ef1 0x48 0xc7 (by decide) (by decide) (by decide) 0x202800) pre_rip
  have f4 : InstrSpec 0x102ef8 [0x48, 0xC7, 0xC1, 0xE0, 0x27, 0x20, 0x00] (fun s => s.RIP = 0x102ef8) (movR64Imm32Effect 0x102ef8 1 0x2027e0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x102ef8 1 0x2027e0).toInstrSpec (mov_r64_imm32_effect_step 0x102ef8 0x48 0xc1 (by decide) (by decide) (by decide) 0x2027e0) pre_rip
  have f5 : InstrSpec 0x102eff [0x49, 0xC7, 0xC0, 0x10, 0x28, 0x20, 0x00] (fun s => s.RIP = 0x102eff) (movR64Imm32Effect 0x102eff 8 0x202810)
      [] [] [.reg 8, .rip] :=
    (movR64Imm32Effect_footprint 0x102eff 8 0x202810).toInstrSpec (mov_r64_imm32_effect_step 0x102eff 0x49 0xc0 (by decide) (by decide) (by decide) 0x202810) pre_rip
  have f6 : InstrSpec 0x102f06 [0xE8, 0x95, 0x66, 0x02, 0x00] (PushPre 0x102f06 5) (callEffect (fun _ => 0x1295a0) 0x102f0b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102f06 0x1295a0 0x102f0b).toInstrSpec (call_rel32_effect_step 0x102f06 0x26695 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x102ee4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 54), (4, 4), (5, 5)]) (p' := 0x102eec) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 54), (4, 4), (5, 5), (6, 56)]) (p' := 0x102ef1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 54), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x102ef8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (2, 54), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x102eff) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 60), (2, 54), (4, 4), (5, 5), (6, 56), (7, 58), (8, 62)]) (p' := 0x102f06) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 60), (2, 54), (4, 64), (5, 5), (6, 56), (7, 58), (8, 62)]) (p' := 0x1295a0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l102ed9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102ed9 :=
  Rest.liftedBlock (rest_l102ed9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102ed9 x hx)

theorem rest_l102f0b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102f0b bytes_l102f0b) (entryMap (live .l102f0b))
      4 0x102f0b bytes_l102f0b b_l102f0b := by
  have f0 : InstrSpec 0x102f0b [0x48, 0x8B, 0x14, 0xCD, 0xB8, 0x22, 0x20, 0x00] (LoadPre 0x102f0b (fun s => AddrMode.addr (.abs (some 1) 3 0x2022b8) s (0x102f0b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102f0b 2 (.abs (some 1) 3 0x2022b8))
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x102f0b 2 (.abs (some 1) 3 0x2022b8)).toInstrSpec (mov_r64_m64_effect_step 0x102f0b 0x48 (by decide) 2 (.abs (some 1) 3 0x2022b8) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x102f13 [0x48, 0x8D, 0xB4, 0x24, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102f13) (leaR64Effect 0x102f13 6 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102f13 6 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (lea_r64_effect_step 0x102f13 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102f1b [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x102f1b) (movR64R64Effect 0x102f1b 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102f1b 7 3).toInstrSpec (mov_r64_r64_effect_step 0x102f1b 0x48 0xdf (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102f1e [0xFF, 0x15, 0xAC, 0x0E, 0x10, 0x00] (GoesTo (CallMemPre 0x102f1e (.rip 0x100eac)) (callEffect (callMemPtr 0x102f1e (.rip 0x100eac)) (0x102f1e + BitVec.ofNat 64 (callMemLen (.rip 0x100eac)))) 0x12a820) (callEffect (callMemPtr 0x102f1e (.rip 0x100eac)) (0x102f1e + BitVec.ofNat 64 (callMemLen (.rip 0x100eac))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x102f1e (.rip 0x100eac)).toInstrSpec (call_m64_effect_step 0x102f1e (.rip 0x100eac) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f13) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f1b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f1e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 59), (5, 5), (6, 55), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l102f0b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102f0b :=
  Rest.liftedBlock (rest_l102f0b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102f0b x hx)

theorem rest_l102f24 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102f24 bytes_l102f24) (entryMap (live .l102f24))
      2 0x102f24 bytes_l102f24 b_l102f24 := by
  have f0 : InstrSpec 0x102f24 [0x31, 0xC0] (fun s => s.RIP = 0x102f24) (xorR32R32Effect 0x102f24 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x102f24 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x102f24 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f26) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x102f26 0xffffff3c (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l102f24 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102f24 :=
  Rest.liftedBlock (rest_l102f24 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102f24 x hx)

theorem rest_l102f2b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102f2b bytes_l102f2b) (entryMap (live .l102f2b))
      1 0x102f2b bytes_l102f2b b_l102f2b := by
  have f0 : InstrSpec 0x102f2b [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x102f2b) (movR64R64Effect 0x102f2b 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102f2b 6 4).toInstrSpec (mov_r64_r64_effect_step 0x102f2b 0x48 0xe6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8)]) (p' := 0x102f2e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l102f2b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102f2b :=
  Rest.liftedBlock (rest_l102f2b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102f2b x hx)

theorem rest_l102f2e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102f2e bytes_l102f2e) (entryMap (live .l102f2e))
      5 0x102f2e bytes_l102f2e b_l102f2e := by
  have f0 : InstrSpec 0x102f2e [0x31, 0xFF] (fun s => s.RIP = 0x102f2e) (xorR32R32Effect 0x102f2e 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x102f2e 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x102f2e 0xff (by decide)) pre_rip
  have f1 : InstrSpec 0x102f30 [0x48, 0xC7, 0xC2, 0xE8, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x102f30) (movR64Imm32Effect 0x102f30 2 0x2022e8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x102f30 2 0x2022e8).toInstrSpec (mov_r64_imm32_effect_step 0x102f30 0x48 0xc2 (by decide) (by decide) (by decide) 0x2022e8) pre_rip
  have f2 : InstrSpec 0x102f37 [0x31, 0xC9] (fun s => s.RIP = 0x102f37) (xorR32R32Effect 0x102f37 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x102f37 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x102f37 0xc9 (by decide)) pre_rip
  have f3 : InstrSpec 0x102f39 [0x49, 0xC7, 0xC1, 0xF0, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x102f39) (movR64Imm32Effect 0x102f39 9 0x2022f0)
      [] [] [.reg 9, .rip] :=
    (movR64Imm32Effect_footprint 0x102f39 9 0x2022f0).toInstrSpec (mov_r64_imm32_effect_step 0x102f39 0x49 0xc1 (by decide) (by decide) (by decide) 0x2022f0) pre_rip
  have f4 : InstrSpec 0x102f40 [0xE8, 0xC3, 0x24, 0x01, 0x00] (PushPre 0x102f40 5) (callEffect (fun _ => 0x115408) 0x102f45)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102f40 0x115408 0x102f45).toInstrSpec (call_rel32_effect_step 0x102f40 0x124c3 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8)]) (p' := 0x102f30) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8)]) (p' := 0x102f37) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (2, 55), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8)]) (p' := 0x102f39) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 57), (2, 55), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 59)]) (p' := 0x102f40) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 57), (2, 55), (4, 61), (5, 5), (6, 6), (7, 53), (8, 8), (9, 59)]) (p' := 0x115408) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l102f2e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102f2e :=
  Rest.liftedBlock (rest_l102f2e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102f2e x hx)

theorem rest_l102f45 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102f45 bytes_l102f45) (entryMap (live .l102f45))
      4 0x102f45 bytes_l102f45 b_l102f45 := by
  have f0 : InstrSpec 0x102f45 [0x48, 0xC7, 0x04, 0x24, 0x98, 0x24, 0x20, 0x00] (StorePre 0x102f45 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102f45 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x102f45 (.sib 4 none 0 .none) 0x202498)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102f45 (.sib 4 none 0 .none) 0x202498).toInstrSpec (mov_m64_imm32_effect_step 0x102f45 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x202498) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x102f4d [0x48, 0xC7, 0x44, 0x24, 0x08, 0x90, 0xA1, 0x12, 0x00] (StorePre 0x102f4d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x102f4d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102f4d (.sib 4 none 0 (.d8 0x8)) 0x12a190)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102f4d (.sib 4 none 0 (.d8 0x8)) 0x12a190).toInstrSpec (mov_m64_imm32_effect_step 0x102f4d 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x12a190) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x102f56 [0x48, 0x8D, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102f56) (leaR64Effect 0x102f56 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x102f56 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (lea_r64_effect_step 0x102f56 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x102f4d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5)]) (p' := 0x102f56) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (4, 4), (5, 5)]) (p' := 0x102f5e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x102f5e 0x19 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l102f45 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102f45 :=
  Rest.liftedBlock (rest_l102f45 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102f45 x hx)

theorem rest_l102f60 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102f60 bytes_l102f60) (entryMap (live .l102f60))
      3 0x102f60 bytes_l102f60 b_l102f60 := by
  have f0 : InstrSpec 0x102f60 [0x48, 0xC7, 0x04, 0x24, 0x98, 0x24, 0x20, 0x00] (StorePre 0x102f60 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102f60 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x102f60 (.sib 4 none 0 .none) 0x202498)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102f60 (.sib 4 none 0 .none) 0x202498).toInstrSpec (mov_m64_imm32_effect_step 0x102f60 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x202498) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x102f68 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x90, 0xA1, 0x12, 0x00] (StorePre 0x102f68 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x102f68 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102f68 (.sib 4 none 0 (.d8 0x8)) 0x12a190)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102f68 (.sib 4 none 0 (.d8 0x8)) 0x12a190).toInstrSpec (mov_m64_imm32_effect_step 0x102f68 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x12a190) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x102f71 [0x48, 0x8D, 0x84, 0x24, 0xF8, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x102f71) (leaR64Effect 0x102f71 0 (.sib 4 none 0 (.d32 0x2f8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x102f71 0 (.sib 4 none 0 (.d32 0x2f8))).toInstrSpec (lea_r64_effect_step 0x102f71 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x2f8)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x102f68) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5)]) (p' := 0x102f71) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (4, 4), (5, 5)]) (p' := 0x102f79) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l102f60 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102f60 :=
  Rest.liftedBlock (rest_l102f60 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102f60 x hx)

theorem rest_l102f79 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102f79 bytes_l102f79) (entryMap (live .l102f79))
      6 0x102f79 bytes_l102f79 b_l102f79 := by
  have f0 : InstrSpec 0x102f79 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x102f79 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102f79 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102f79 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102f79 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x102f79 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x102f7e [0x48, 0xC7, 0x44, 0x24, 0x18, 0x90, 0xA1, 0x12, 0x00] (StorePre 0x102f7e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102f7e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102f7e (.sib 4 none 0 (.d8 0x18)) 0x12a190)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102f7e (.sib 4 none 0 (.d8 0x18)) 0x12a190).toInstrSpec (mov_m64_imm32_effect_step 0x102f7e 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x12a190) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x102f87 [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x102f87) (movR64R64Effect 0x102f87 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102f87 6 4).toInstrSpec (mov_r64_r64_effect_step 0x102f87 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102f8a [0x48, 0xC7, 0xC7, 0x8F, 0x02, 0x20, 0x00] (fun s => s.RIP = 0x102f8a) (movR64Imm32Effect 0x102f8a 7 0x20028f)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x102f8a 7 0x20028f).toInstrSpec (mov_r64_imm32_effect_step 0x102f8a 0x48 0xc7 (by decide) (by decide) (by decide) 0x20028f) pre_rip
  have f4 : InstrSpec 0x102f91 [0x48, 0xC7, 0xC2, 0x18, 0x25, 0x20, 0x00] (fun s => s.RIP = 0x102f91) (movR64Imm32Effect 0x102f91 2 0x202518)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x102f91 2 0x202518).toInstrSpec (mov_r64_imm32_effect_step 0x102f91 0x48 0xc2 (by decide) (by decide) (by decide) 0x202518) pre_rip
  have f5 : InstrSpec 0x102f98 [0xE8, 0xD3, 0x67, 0x02, 0x00] (PushPre 0x102f98 5) (callEffect (fun _ => 0x129770) 0x102f9d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102f98 0x129770 0x102f9d).toInstrSpec (call_rel32_effect_step 0x102f98 0x267d3 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (4, 4), (5, 5)]) (p' := 0x102f7e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (5, 5)]) (p' := 0x102f87) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (4, 4), (5, 5), (6, 55)]) (p' := 0x102f8a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (4, 4), (5, 5), (6, 55), (7, 57)]) (p' := 0x102f91) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 59), (4, 4), (5, 5), (6, 55), (7, 57)]) (p' := 0x102f98) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 59), (4, 61), (5, 5), (6, 55), (7, 57)]) (p' := 0x129770) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l102f79 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102f79 :=
  Rest.liftedBlock (rest_l102f79 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102f79 x hx)

theorem rest_l102f9d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102f9d bytes_l102f9d) (entryMap (live .l102f9d))
      2 0x102f9d bytes_l102f9d b_l102f9d := by
  have f0 : InstrSpec 0x102f9d [0x48, 0x8D, 0xB4, 0x24, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102f9d) (leaR64Effect 0x102f9d 6 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102f9d 6 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (lea_r64_effect_step 0x102f9d 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8)]) (p' := 0x102fa5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x102fa5 0x87 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l102f9d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102f9d :=
  Rest.liftedBlock (rest_l102f9d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102f9d x hx)

theorem rest_l102fa7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102fa7 bytes_l102fa7) (entryMap (live .l102fa7))
      2 0x102fa7 bytes_l102fa7 b_l102fa7 := by
  have f0 : InstrSpec 0x102fa7 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x102fa7) (movR64R64Effect 0x102fa7 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102fa7 7 4).toInstrSpec (mov_r64_r64_effect_step 0x102fa7 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102faa [0xE8, 0xD1, 0xD1, 0xFF, 0xFF] (PushPre 0x102faa 5) (callEffect (fun _ => 0x100180) 0x102faf)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102faa 0x100180 0x102faf).toInstrSpec (call_rel32_effect_step 0x102faa 0xffffd1d1 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102faa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100180) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l102fa7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102fa7 :=
  Rest.liftedBlock (rest_l102fa7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102fa7 x hx)

theorem rest_l102faf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102faf bytes_l102faf) (entryMap (live .l102faf))
      1 0x102faf bytes_l102faf b_l102faf := by
  have f0 : InstrSpec 0x102faf [0xE8, 0x7C, 0xDA, 0xFF, 0xFF] (PushPre 0x102faf 5) (callEffect (fun _ => 0x100a30) 0x102fb4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102faf 0x100a30 0x102fb4).toInstrSpec (call_rel32_effect_step 0x102faf 0xffffda7c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := []) (p' := 0x100a30) f0 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 54) (by decide) (by decide) rfl rfl

theorem block_l102faf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102faf :=
  Rest.liftedBlock (rest_l102faf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102faf x hx)

theorem rest_l102fb4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102fb4 bytes_l102fb4) (entryMap (live .l102fb4))
      14 0x102fb4 bytes_l102fb4 b_l102fb4 := by
  have f0 : InstrSpec 0x102fb4 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102fb4) (fun _ => nopEffect 0x102fb4 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x102fb4 10).toInstrSpec (nop_m_effect_step 0x102fb4 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102fbe [0x66, 0x90] (fun s => s.RIP = 0x102fbe) (fun _ => nopEffect 0x102fbe 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x102fbe 2).toInstrSpec (nop_66_effect_step 0x102fbe) pre_rip
  have f2 : InstrSpec 0x102fc0 [0x41, 0x57] (PushPre 0x102fc0 2) (pushR64Effect 0x102fc0 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102fc0 2 15).toInstrSpec (push_r64_rex_effect_step 0x102fc0 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x102fc2 [0x41, 0x56] (PushPre 0x102fc2 2) (pushR64Effect 0x102fc2 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102fc2 2 14).toInstrSpec (push_r64_rex_effect_step 0x102fc2 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x102fc4 [0x41, 0x54] (PushPre 0x102fc4 2) (pushR64Effect 0x102fc4 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102fc4 2 12).toInstrSpec (push_r64_rex_effect_step 0x102fc4 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x102fc6 [0x53] (PushPre 0x102fc6 1) (pushR64Effect 0x102fc6 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102fc6 1 3).toInstrSpec (push_r64_effect_step 0x102fc6 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x102fc7 [0x48, 0x81, 0xEC, 0xF8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102fc7) (subR64Imm32Effect 0x102fc7 4 0x1f8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x102fc7 4 0x1f8).toInstrSpec (sub_r64_imm32_effect_step 0x102fc7 0x48 0xec 0x1f8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x102fce [0x49, 0x89, 0xCF] (fun s => s.RIP = 0x102fce) (movR64R64Effect 0x102fce 15 1)
      [.gpr 1] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x102fce 15 1).toInstrSpec (mov_r64_r64_effect_step 0x102fce 0x49 0xcf (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x102fd1 [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x102fd1) (movR64R64Effect 0x102fd1 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x102fd1 3 2).toInstrSpec (mov_r64_r64_effect_step 0x102fd1 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x102fd4 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x102fd4) (movR64R64Effect 0x102fd4 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x102fd4 14 6).toInstrSpec (mov_r64_r64_effect_step 0x102fd4 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x102fd7 [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x102fd7) (movR64R64Effect 0x102fd7 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102fd7 6 7).toInstrSpec (mov_r64_r64_effect_step 0x102fd7 0x48 0xfe (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x102fda [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x102fda) (leaR64Effect 0x102fda 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102fda 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x102fda 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x102fdf [0xBA, 0x41, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102fdf) (movR32Imm32Effect 0x102fdf 5 2 0x41)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x102fdf 5 2 0x41).toInstrSpec (mov_r32_imm32_effect_step 0x102fdf 0xba (by decide) 0x41) pre_rip
  have f13 : InstrSpec 0x102fe4 [0xE8, 0xA7, 0x33, 0x00, 0x00] (PushPre 0x102fe4 5) (callEffect (fun _ => 0x106390) 0x102fe9)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102fe4 0x106390 0x102fe9).toInstrSpec (call_rel32_effect_step 0x102fe4 0x33a7 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fbe) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fc0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fc2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fc4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fc6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fc7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fce) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fd1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fd4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fd7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 67), (4, 63), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fda) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 67), (4, 63), (5, 5), (6, 71), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fdf) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 75), (3, 67), (4, 63), (5, 5), (6, 71), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fe4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 75), (3, 67), (4, 77), (5, 5), (6, 71), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106390) f13 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 79) (by decide) (by decide) rfl rfl

theorem block_l102fb4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102fb4 :=
  Rest.liftedBlock (rest_l102fb4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102fb4 x hx)

theorem rest_l102fe9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102fe9 bytes_l102fe9) (entryMap (live .l102fe9))
      2 0x102fe9 bytes_l102fe9 b_l102fe9 := by
  have f0 : InstrSpec 0x102fe9 [0x80, 0x7C, 0x24, 0x08, 0x00] (LoadPre 0x102fe9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x102fe9 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x102fe9 5 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x102fe9 5 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x102fe9 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fee) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x102fee 5 0x414) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102fe9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102fe9 :=
  Rest.liftedBlock (rest_l102fe9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102fe9 x hx)

theorem rest_l102ff4 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102ff4 bytes_l102ff4) (entryMap (live .l102ff4))
      12 0x102ff4 bytes_l102ff4 b_l102ff4 := by
  have f0 : InstrSpec 0x102ff4 [0x48, 0x8D, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102ff4) (leaR64Effect 0x102ff4 0 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x102ff4 0 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x102ff4 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102ffc [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x102ffc) (leaR64Effect 0x102ffc 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102ffc 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x102ffc 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103001 [0xB9, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103001) (movR32Imm32Effect 0x103001 5 1 0xb)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x103001 5 1 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x103001 0xb9 (by decide) 0xb) pre_rip
  have f3 : InstrSpec 0x103006 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x103006) (movR64R64Effect 0x103006 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103006 7 0).toInstrSpec (mov_r64_r64_effect_step 0x103006 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103009 [0xF3, 0x48, 0xA5] (RepPre 0x103009 (RepMovsqPre 0x103009)) (repMovsqEffect 0x103009)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x103009).toInstrSpecOfRuns (rep_movsq_runs hstride 0x103009 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x10300c [0x48, 0x8D, 0xBC, 0x24, 0xA0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10300c) (leaR64Effect 0x10300c 7 (.sib 4 none 0 (.d32 0x1a0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10300c 7 (.sib 4 none 0 (.d32 0x1a0))).toInstrSpec (lea_r64_effect_step 0x10300c 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x1a0)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x103014 [0xB9, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103014) (movR32Imm32Effect 0x103014 5 1 0xb)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x103014 5 1 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x103014 0xb9 (by decide) 0xb) pre_rip
  have f7 : InstrSpec 0x103019 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x103019) (movR64R64Effect 0x103019 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x103019 6 0).toInstrSpec (mov_r64_r64_effect_step 0x103019 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10301c [0xF3, 0x48, 0xA5] (RepPre 0x10301c (RepMovsqPre 0x10301c)) (repMovsqEffect 0x10301c)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10301c).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10301c 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f9 : InstrSpec 0x10301f [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x10301f) (leaR64Effect 0x10301f 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10301f 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10301f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x103024 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x103024) (movR64R64Effect 0x103024 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x103024 6 15).toInstrSpec (mov_r64_r64_effect_step 0x103024 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x103027 [0xE8, 0x94, 0x0A, 0x00, 0x00] (PushPre 0x103027 5) (callEffect (fun _ => 0x103ac0) 0x10302c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103027 0x103ac0 0x10302c).toInstrSpec (call_rel32_effect_step 0x103027 0xa94 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ffc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103001) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103006) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103009) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10300c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103014) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 64), (3, 3), (4, 4), (5, 5), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103019) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 64), (3, 3), (4, 4), (5, 5), (6, 66), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10301c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10301f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103024) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 71), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103027) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (3, 3), (4, 73), (5, 5), (6, 71), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ac0) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l102ff4 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102ff4 :=
  Rest.liftedBlock (rest_l102ff4 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102ff4 x hx)

theorem rest_l10302c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10302c bytes_l10302c) (entryMap (live .l10302c))
      2 0x10302c bytes_l10302c b_l10302c := by
  have f0 : InstrSpec 0x10302c [0x83, 0x7C, 0x24, 0x08, 0x01] (LoadPre 0x10302c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10302c + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x10302c 5 32 (.sib 4 none 0 (.d8 0x8)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x10302c 5 (.sib 4 none 0 (.d8 0x8)) 0x1).toInstrSpec (cmp_m32_imm8_effect_step 0x10302c (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103031) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x103031 4 0x3fb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10302c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10302c :=
  Rest.liftedBlock (rest_l10302c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10302c x hx)

theorem rest_l103037_1 [Bindings] (code : CodeMap) :
    Rest (n := 83) code lifted (codeRange 0x103037 bytes_l103037) [(0, 80), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      8 0x1030c3 bytes_l103037_1 b_l103037_1 := by
  have f20 : InstrSpec 0x1030c3 [0x48, 0xB8, 0x72, 0xF3, 0x6E, 0x3C, 0x3A, 0xF5, 0x4F, 0xA5] (fun s => s.RIP = 0x1030c3) (movR64Imm64Effect 0x1030c3 0 0xa54ff53a3c6ef372)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x1030c3 0 0xa54ff53a3c6ef372).toInstrSpec (mov_r64_imm64_effect_step 0x1030c3 0x48 0xb8 (by decide) (by decide) 0xa54ff53a3c6ef372) pre_rip
  have f21 : InstrSpec 0x1030cd [0x48, 0x89, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00] (StorePre 0x1030cd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1030cd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1030cd 0 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1030cd 0 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_m64_r64_effect_step 0x1030cd 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x1030d5 [0x48, 0xB8, 0x67, 0xE6, 0x09, 0x6A, 0x85, 0xAE, 0x67, 0xBB] (fun s => s.RIP = 0x1030d5) (movR64Imm64Effect 0x1030d5 0 0xbb67ae856a09e667)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x1030d5 0 0xbb67ae856a09e667).toInstrSpec (mov_r64_imm64_effect_step 0x1030d5 0x48 0xb8 (by decide) (by decide) 0xbb67ae856a09e667) pre_rip
  have f23 : InstrSpec 0x1030df [0x48, 0x89, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00] (StorePre 0x1030df 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x1030df + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1030df 0 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1030df 0 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_m64_r64_effect_step 0x1030df 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x1030e7 [0x48, 0xC7, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1030e7 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x1030e7 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1030e7 (.sib 4 none 0 (.d32 0x158)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1030e7 (.sib 4 none 0 (.d32 0x158)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1030e7 0x48 (by decide) (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x1030f3 [0xC6, 0x84, 0x24, 0x37, 0x01, 0x00, 0x00, 0x00] (StorePre 0x1030f3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x137)) s (0x1030f3 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x1030f3 (.sib 4 none 0 (.d32 0x137)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1030f3 (.sib 4 none 0 (.d32 0x137)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1030f3 (.sib 4 none 0 (.d32 0x137)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x1030fb [0x48, 0x83, 0xFB, 0x3F] (fun s => s.RIP = 0x1030fb) (cmpR64Imm8Effect 0x1030fb 3 0x3f)
      [.gpr 3] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1030fb 3 0x3f).toInstrSpec (cmp_r64_imm8_effect_step 0x1030fb 0x48 0xfb 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030cd) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 83), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030d5) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 86), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030df) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 86), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030e7) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 86), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030f3) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 86), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030fb) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f26 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 92) f26 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 93) (ρ' := [(0, 86), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 91), (19, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030ff) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 94) (jcc_rel8_effect_step 0x1030ff 7 0x1d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l103037 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103037 bytes_l103037) (entryMap (live .l103037))
      28 0x103037 bytes_l103037 b_l103037 := by
  have f0 : InstrSpec 0x103037 [0x48, 0x8B, 0x44, 0x24, 0x48] (LoadPre 0x103037 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x103037 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103037 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103037 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x103037 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10303c [0x48, 0x89, 0x84, 0x24, 0x98, 0x01, 0x00, 0x00] (StorePre 0x10303c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x10303c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10303c 0 (.sib 4 none 0 (.d32 0x198)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10303c 0 (.sib 4 none 0 (.d32 0x198))).toInstrSpec (mov_m64_r64_effect_step 0x10303c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x198)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103044 [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x103044 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x103044 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103044 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103044 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x103044 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x103049 [0x48, 0x89, 0x84, 0x24, 0x90, 0x01, 0x00, 0x00] (StorePre 0x103049 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x103049 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103049 0 (.sib 4 none 0 (.d32 0x190)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103049 0 (.sib 4 none 0 (.d32 0x190))).toInstrSpec (mov_m64_r64_effect_step 0x103049 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x190)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x103051 [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x103051 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x103051 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103051 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103051 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x103051 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x103056 [0x48, 0x89, 0x84, 0x24, 0x88, 0x01, 0x00, 0x00] (StorePre 0x103056 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x103056 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103056 0 (.sib 4 none 0 (.d32 0x188)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103056 0 (.sib 4 none 0 (.d32 0x188))).toInstrSpec (mov_m64_r64_effect_step 0x103056 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x188)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10305e [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x10305e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10305e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10305e 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10305e 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10305e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x103063 [0x48, 0x89, 0x84, 0x24, 0x80, 0x01, 0x00, 0x00] (StorePre 0x103063 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x103063 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103063 0 (.sib 4 none 0 (.d32 0x180)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103063 0 (.sib 4 none 0 (.d32 0x180))).toInstrSpec (mov_m64_r64_effect_step 0x103063 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x180)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10306b [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x10306b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10306b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10306b 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10306b 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10306b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x103070 [0x48, 0x89, 0x84, 0x24, 0x78, 0x01, 0x00, 0x00] (StorePre 0x103070 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x103070 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103070 0 (.sib 4 none 0 (.d32 0x178)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103070 0 (.sib 4 none 0 (.d32 0x178))).toInstrSpec (mov_m64_r64_effect_step 0x103070 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x178)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x103078 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x103078 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103078 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103078 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103078 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x103078 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10307d [0x48, 0x89, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00] (StorePre 0x10307d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x10307d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10307d 0 (.sib 4 none 0 (.d32 0x170)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10307d 0 (.sib 4 none 0 (.d32 0x170))).toInstrSpec (mov_m64_r64_effect_step 0x10307d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x103085 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x103085 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103085 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103085 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103085 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x103085 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10308a [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x10308a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10308a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10308a 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10308a 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10308a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10308f [0x48, 0x89, 0x8C, 0x24, 0x68, 0x01, 0x00, 0x00] (StorePre 0x10308f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x10308f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10308f 1 (.sib 4 none 0 (.d32 0x168)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10308f 1 (.sib 4 none 0 (.d32 0x168))).toInstrSpec (mov_m64_r64_effect_step 0x10308f 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x168)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x103097 [0x48, 0x89, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00] (StorePre 0x103097 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x103097 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103097 0 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103097 0 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (mov_m64_r64_effect_step 0x103097 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x10309f [0x48, 0xB8, 0xAB, 0xD9, 0x83, 0x1F, 0x19, 0xCD, 0xE0, 0x5B] (fun s => s.RIP = 0x10309f) (movR64Imm64Effect 0x10309f 0 0x5be0cd191f83d9ab)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x10309f 0 0x5be0cd191f83d9ab).toInstrSpec (mov_r64_imm64_effect_step 0x10309f 0x48 0xb8 (by decide) (by decide) 0x5be0cd191f83d9ab) pre_rip
  have f17 : InstrSpec 0x1030a9 [0x48, 0x89, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00] (StorePre 0x1030a9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x1030a9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1030a9 0 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1030a9 0 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (mov_m64_r64_effect_step 0x1030a9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1030b1 [0x48, 0xB8, 0x7F, 0x52, 0x0E, 0x51, 0x8C, 0x68, 0x05, 0x9B] (fun s => s.RIP = 0x1030b1) (movR64Imm64Effect 0x1030b1 0 0x9b05688c510e527f)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x1030b1 0 0x9b05688c510e527f).toInstrSpec (mov_r64_imm64_effect_step 0x1030b1 0x48 0xb8 (by decide) (by decide) 0x9b05688c510e527f) pre_rip
  have f19 : InstrSpec 0x1030bb [0x48, 0x89, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00] (StorePre 0x1030bb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x1030bb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1030bb 0 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1030bb 0 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (mov_m64_r64_effect_step 0x1030bb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10303c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103044) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103049) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103051) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103056) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10305e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103063) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10306b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103070) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103078) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10307d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103085) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10308a) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10308f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103097) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10309f) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030a9) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030b1) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030bb) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 80), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030c3) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l103037_1 code

theorem block_l103037 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103037 :=
  Rest.liftedBlock (rest_l103037 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103037 x hx)

theorem rest_l103101 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103101 bytes_l103101) (entryMap (live .l103101))
      4 0x103101 bytes_l103101 b_l103101 := by
  have f0 : InstrSpec 0x103101 [0x48, 0x8D, 0xBC, 0x24, 0xF8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103101) (leaR64Effect 0x103101 7 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103101 7 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (lea_r64_effect_step 0x103101 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103109 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x103109) (movR64R64Effect 0x103109 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x103109 6 14).toInstrSpec (mov_r64_r64_effect_step 0x103109 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10310c [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x10310c) (movR64R64Effect 0x10310c 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10310c 2 3).toInstrSpec (mov_r64_r64_effect_step 0x10310c 0x48 0xda (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10310f [0xFF, 0x15, 0xBB, 0x0C, 0x10, 0x00] (GoesTo (CallMemPre 0x10310f (.rip 0x100cbb)) (callEffect (callMemPtr 0x10310f (.rip 0x100cbb)) (0x10310f + BitVec.ofNat 64 (callMemLen (.rip 0x100cbb)))) 0x12a820) (callEffect (callMemPtr 0x10310f (.rip 0x100cbb)) (0x10310f + BitVec.ofNat 64 (callMemLen (.rip 0x100cbb))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x10310f (.rip 0x100cbb)).toInstrSpec (call_m64_effect_step 0x10310f (.rip 0x100cbb) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103109) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10310c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10310f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l103101 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103101 :=
  Rest.liftedBlock (rest_l103101 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103101 x hx)

theorem rest_l103115 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103115 bytes_l103115) (entryMap (live .l103115))
      2 0x103115 bytes_l103115 b_l103115 := by
  have f0 : InstrSpec 0x103115 [0x88, 0x9C, 0x24, 0x37, 0x01, 0x00, 0x00] (StorePre 0x103115 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x137)) s (0x103115 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x103115 7 3 (.sib 4 none 0 (.d32 0x137)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x103115 7 3 (.sib 4 none 0 (.d32 0x137))).toInstrSpec (mov_m8_r8_effect_step 0x103115 3 (by decide) (.sib 4 none 0 (.d32 0x137)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10311c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 54) (jmp_rel8_effect_step 0x10311c 0x52 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103115 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103115 :=
  Rest.liftedBlock (rest_l103115 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103115 x hx)

theorem rest_l10311e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10311e bytes_l10311e) (entryMap (live .l10311e))
      11 0x10311e bytes_l10311e b_l10311e := by
  have f0 : InstrSpec 0x10311e [0x48, 0x8D, 0xBC, 0x24, 0x38, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10311e) (leaR64Effect 0x10311e 7 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10311e 7 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (lea_r64_effect_step 0x10311e 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103126 [0x49, 0xBF, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x103126) (movR64Imm64Effect 0x103126 15 0x7fffffffffffffc0)
      [] [] [.reg 15, .rip] :=
    (movR64Imm64Effect_footprint 0x103126 15 0x7fffffffffffffc0).toInstrSpec (mov_r64_imm64_effect_step 0x103126 0x49 0xbf (by decide) (by decide) 0x7fffffffffffffc0) pre_rip
  have f2 : InstrSpec 0x103130 [0x49, 0x21, 0xDF] (fun s => s.RIP = 0x103130) (andR64R64Effect 0x103130 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103130 15 3).toInstrSpec (and_r64_r64_effect_step 0x103130 0x49 0xdf (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103133 [0x41, 0x89, 0xDC] (fun s => s.RIP = 0x103133) (movR32R32Effect 0x103133 3 12 3)
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x103133 3 12 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x103133 0x41 0xdc (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103136 [0x41, 0x83, 0xE4, 0x3F] (fun s => s.RIP = 0x103136) (andR32Imm8Effect 0x103136 4 12 0x3f)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x103136 4 12 0x3f).toInstrSpec (and_r32_imm8_rex_effect_step 0x103136 0x41 0xe4 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10313a [0x4D, 0x01, 0xF7] (fun s => s.RIP = 0x10313a) (addR64R64Effect 0x10313a 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10313a 15 14).toInstrSpec (add_r64_r64_effect_step 0x10313a 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10313d [0x48, 0xC1, 0xEB, 0x06] (fun s => s.RIP = 0x10313d) (shrR64Effect 0x10313d 4 3 6)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x10313d 4 3 6).toInstrSpec (shr_r64_imm8_effect_step 0x10313d 0x48 0xeb 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103141 [0x48, 0x89, 0x9C, 0x24, 0x58, 0x01, 0x00, 0x00] (StorePre 0x103141 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x103141 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103141 3 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103141 3 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (mov_m64_r64_effect_step 0x103141 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x103149 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x103149) (movR64R64Effect 0x103149 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x103149 6 14).toInstrSpec (mov_r64_r64_effect_step 0x103149 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10314c [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x10314c) (movR64R64Effect 0x10314c 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10314c 2 3).toInstrSpec (mov_r64_r64_effect_step 0x10314c 0x48 0xda (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10314f [0xE8, 0x8C, 0xE7, 0x01, 0x00] (PushPre 0x10314f 5) (callEffect (fun _ => 0x1218e0) 0x103154)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10314f 0x1218e0 0x103154).toInstrSpec (call_rel32_effect_step 0x10314f 0x1e78c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103126) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103130) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103133) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103136) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10313a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10313d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (3, 65), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103141) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (3, 65), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103149) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (3, 65), (4, 4), (5, 5), (6, 68), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10314c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 65), (4, 4), (5, 5), (6, 68), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10314f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 65), (4, 72), (5, 5), (6, 68), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 74) (by decide) (by decide) rfl rfl

theorem block_l10311e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10311e :=
  Rest.liftedBlock (rest_l10311e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10311e x hx)

theorem rest_l103154 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103154 bytes_l103154) (entryMap (live .l103154))
      5 0x103154 bytes_l103154 b_l103154 := by
  have f0 : InstrSpec 0x103154 [0x44, 0x88, 0xA4, 0x24, 0x37, 0x01, 0x00, 0x00] (StorePre 0x103154 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x137)) s (0x103154 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x103154 8 12 (.sib 4 none 0 (.d32 0x137)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x103154 8 12 (.sib 4 none 0 (.d32 0x137))).toInstrSpec (mov_m8_r8_rex_effect_step 0x103154 0x44 (by decide) 4 (.sib 4 none 0 (.d32 0x137)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10315c [0x48, 0x8D, 0xBC, 0x24, 0xF8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10315c) (leaR64Effect 0x10315c 7 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10315c 7 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (lea_r64_effect_step 0x10315c 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103164 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x103164) (movR64R64Effect 0x103164 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x103164 6 15).toInstrSpec (mov_r64_r64_effect_step 0x103164 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103167 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x103167) (movR64R64Effect 0x103167 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x103167 2 12).toInstrSpec (mov_r64_r64_effect_step 0x103167 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10316a [0xFF, 0x15, 0x60, 0x0C, 0x10, 0x00] (GoesTo (CallMemPre 0x10316a (.rip 0x100c60)) (callEffect (callMemPtr 0x10316a (.rip 0x100c60)) (0x10316a + BitVec.ofNat 64 (callMemLen (.rip 0x100c60)))) 0x12a820) (callEffect (callMemPtr 0x10316a (.rip 0x100c60)) (0x10316a + BitVec.ofNat 64 (callMemLen (.rip 0x100c60))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x10316a (.rip 0x100c60)).toInstrSpec (call_m64_effect_step 0x10316a (.rip 0x100c60) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10315c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103164) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 56), (7, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103167) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 58), (3, 3), (4, 4), (5, 5), (6, 56), (7, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10316a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 58), (3, 3), (4, 60), (5, 5), (6, 56), (7, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l103154 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103154 :=
  Rest.liftedBlock (rest_l103154 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103154 x hx)

theorem rest_l103170 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103170 bytes_l103170) (entryMap (live .l103170))
      19 0x103170 bytes_l103170 b_l103170 := by
  have f0 : InstrSpec 0x103170 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x103170) (leaR64Effect 0x103170 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103170 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x103170 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103175 [0x48, 0x8D, 0xB4, 0x24, 0xF8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103175) (leaR64Effect 0x103175 6 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x103175 6 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (lea_r64_effect_step 0x103175 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10317d [0xB9, 0x0D, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10317d) (movR32Imm32Effect 0x10317d 5 1 0xd)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10317d 5 1 0xd).toInstrSpec (mov_r32_imm32_effect_step 0x10317d 0xb9 (by decide) 0xd) pre_rip
  have f3 : InstrSpec 0x103182 [0xF3, 0x48, 0xA5] (RepPre 0x103182 (RepMovsqPre 0x103182)) (repMovsqEffect 0x103182)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x103182).toInstrSpecOfRuns (rep_movsq_runs hstride 0x103182 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x103185 [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x47] (LoadPre 0x103185 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x103185 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x103185 6 15 (.sib 4 none 0 (.d8 0x47)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x103185 6 15 (.sib 4 none 0 (.d8 0x47))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x103185 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x47)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10318b [0x48, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x10318b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10318b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10318b 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10318b 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x10318b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x103190 [0x48, 0xC1, 0xE0, 0x09] (fun s => s.RIP = 0x103190) (shlR64Effect 0x103190 4 0 9)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x103190 4 0 9).toInstrSpec (shl_r64_imm8_effect_step 0x103190 0x48 0xe0 0x9 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103194 [0x4D, 0x89, 0xFE] (fun s => s.RIP = 0x103194) (movR64R64Effect 0x103194 14 15)
      [.gpr 15] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x103194 14 15).toInstrSpec (mov_r64_r64_effect_step 0x103194 0x4d 0xfe (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x103197 [0x42, 0xC6, 0x44, 0x3C, 0x08, 0x80] (StorePre 0x103197 6 (fun s => AddrMode.addr (.sib 4 (some 15) 0 (.d8 0x8)) s (0x103197 + BitVec.ofNat 64 6)) 1) (movM8Imm8RexEffect 0x103197 (.sib 4 (some 15) 0 (.d8 0x8)) 0x80)
      [.gpr 4, .gpr 15] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x103197 (.sib 4 (some 15) 0 (.d8 0x8)) 0x80).toInstrSpec (mov_m8_imm8_rex_effect_step 0x103197 0x42 (by decide) (.sib 4 (some 15) 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x80) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10319d [0x4A, 0x8D, 0x3C, 0x3C] (fun s => s.RIP = 0x10319d) (leaR64Effect 0x10319d 7 (.sib 4 (some 15) 0 .none))
      [.gpr 4, .gpr 15] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10319d 7 (.sib 4 (some 15) 0 .none)).toInstrSpec (lea_r64_effect_step 0x10319d 0x4a (by decide) 7 (.sib 4 (some 15) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1031a1 [0x48, 0x83, 0xC7, 0x09] (fun s => s.RIP = 0x1031a1) (addR64Imm8Effect 0x1031a1 7 0x9)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1031a1 7 0x9).toInstrSpec (add_r64_imm8_effect_step 0x1031a1 0x48 0xc7 0x9 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1031a5 [0x41, 0xC1, 0xE7, 0x03] (fun s => s.RIP = 0x1031a5) (shlR32Effect 0x1031a5 4 15 3)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shlR32Effect_footprint 0x1031a5 4 15 3).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1031a5 0x41 0xe7 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1031a9 [0x49, 0x09, 0xC7] (fun s => s.RIP = 0x1031a9) (orR64R64Effect 0x1031a9 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1031a9 15 0).toInstrSpec (or_r64_r64_effect_step 0x1031a9 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1031ac [0x48, 0x8D, 0x5C, 0x24, 0x48] (fun s => s.RIP = 0x1031ac) (leaR64Effect 0x1031ac 3 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x1031ac 3 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x1031ac 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1031b1 [0x49, 0x0F, 0xCF] (fun s => s.RIP = 0x1031b1) (bswapR64Effect 0x1031b1 3 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (bswapR64Effect_footprint 0x1031b1 3 15).toInstrSpec (bswap_r64_effect_step 0x1031b1 0x49 (by decide) 0xcf (by decide)) pre_rip
  have f15 : InstrSpec 0x1031b4 [0x49, 0x83, 0xF6, 0x3F] (fun s => s.RIP = 0x1031b4) (xorR64Imm8Effect 0x1031b4 14 0x3f)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR64Imm8Effect_footprint 0x1031b4 14 0x3f).toInstrSpec (xor_r64_imm8_effect_step 0x1031b4 0x49 0xf6 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1031b8 [0x31, 0xF6] (fun s => s.RIP = 0x1031b8) (xorR32R32Effect 0x1031b8 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1031b8 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x1031b8 0xf6 (by decide)) pre_rip
  have f17 : InstrSpec 0x1031ba [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x1031ba) (movR64R64Effect 0x1031ba 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1031ba 2 14).toInstrSpec (mov_r64_r64_effect_step 0x1031ba 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1031bd [0xFF, 0x15, 0x4D, 0x0C, 0x10, 0x00] (GoesTo (CallMemPre 0x1031bd (.rip 0x100c4d)) (callEffect (callMemPtr 0x1031bd (.rip 0x100c4d)) (0x1031bd + BitVec.ofNat 64 (callMemLen (.rip 0x100c4d)))) 0x12a700) (callEffect (callMemPtr 0x1031bd (.rip 0x100c4d)) (0x1031bd + BitVec.ofNat 64 (callMemLen (.rip 0x100c4d))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1031bd (.rip 0x100c4d)).toInstrSpec (call_m64_effect_step 0x1031bd (.rip 0x100c4d) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a700
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103175) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10317d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103182) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103185) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10318b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103190) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103194) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103197) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10319d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (7, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031a1) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031a5) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031a9) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031ac) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 65), (3, 78), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031b1) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 65), (3, 78), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031b4) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 65), (3, 78), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 82), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031b8) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 65), (3, 78), (4, 4), (5, 5), (6, 84), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 82), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031ba) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 65), (2, 86), (3, 78), (4, 4), (5, 5), (6, 84), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 82), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031bd) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 65), (2, 86), (3, 78), (4, 88), (5, 5), (6, 84), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 82), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a700) f18 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 90) (by decide) (by decide) rfl rfl

theorem block_l103170 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103170 :=
  Rest.liftedBlock (rest_l103170 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103170 x hx)

theorem rest_l1031c3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1031c3 bytes_l1031c3) (entryMap (live .l1031c3))
      2 0x1031c3 bytes_l1031c3 b_l1031c3 := by
  have f0 : InstrSpec 0x1031c3 [0x49, 0x83, 0xFE, 0x07] (fun s => s.RIP = 0x1031c3) (cmpR64Imm8Effect 0x1031c3 14 0x7)
      [.gpr 14] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1031c3 14 0x7).toInstrSpec (cmp_r64_imm8_effect_step 0x1031c3 0x49 0xfe 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031c7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x1031c7 7 0xbc) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1031c3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1031c3 :=
  Rest.liftedBlock (rest_l1031c3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1031c3 x hx)

theorem rest_l1031cd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1031cd bytes_l1031cd) (entryMap (live .l1031cd))
      20 0x1031cd bytes_l1031cd b_l1031cd := by
  have f0 : InstrSpec 0x1031cd [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x1031cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1031cd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1031cd 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1031cd 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1031cd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1031d2 [0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x1031d2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1031d2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1031d2 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1031d2 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x1031d2 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1031da [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x1031da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1031da + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1031da 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1031da 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1031da 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1031df [0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x1031df 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1031df + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1031df 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1031df 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x1031df 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1031e7 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x1031e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1031e7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1031e7 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1031e7 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1031e7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1031ec [0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x1031ec 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1031ec + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1031ec 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1031ec 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x1031ec 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1031f4 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x1031f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1031f4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1031f4 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1031f4 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1031f4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1031f9 [0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x1031f9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1031f9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1031f9 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1031f9 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x1031f9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x103201 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x103201 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103201 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103201 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103201 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x103201 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x103206 [0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x103206 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x103206 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103206 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103206 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x103206 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10320e [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x10320e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10320e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10320e 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10320e 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10320e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x103213 [0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x103213 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x103213 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103213 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103213 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x103213 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10321b [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x10321b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10321b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10321b 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10321b 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10321b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x103220 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x103220 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103220 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103220 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x103220 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x103220 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x103225 [0x48, 0x89, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x103225 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x103225 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103225 1 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103225 1 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x103225 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x10322d [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x10322d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10322d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10322d 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10322d 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x10322d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x103235 [0x48, 0x8D, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103235) (leaR64Effect 0x103235 6 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x103235 6 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x103235 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10323d [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10323d) (movR32Imm32Effect 0x10323d 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10323d 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x10323d 0xba (by decide) 0x1) pre_rip
  have f18 : InstrSpec 0x103242 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x103242) (movR64R64Effect 0x103242 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103242 7 3).toInstrSpec (mov_r64_r64_effect_step 0x103242 0x48 0xdf (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x103245 [0xE8, 0x96, 0xE6, 0x01, 0x00] (PushPre 0x103245 5) (callEffect (fun _ => 0x1218e0) 0x10324a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103245 0x1218e0 0x10324a).toInstrSpec (call_rel32_effect_step 0x103245 0x1e696 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031d2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031da) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031df) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031e7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031ec) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031f4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031f9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103201) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103206) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10320e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103213) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10321b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103220) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103225) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10322d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103235) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (6, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10323d) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 71), (1, 73), (2, 79), (3, 3), (4, 4), (5, 5), (6, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103242) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 71), (1, 73), (2, 79), (3, 3), (4, 4), (5, 5), (6, 77), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103245) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 71), (1, 73), (2, 79), (3, 3), (4, 83), (5, 5), (6, 77), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem block_l1031cd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1031cd :=
  Rest.liftedBlock (rest_l1031cd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1031cd x hx)

theorem rest_l10324a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10324a bytes_l10324a) (entryMap (live .l10324a))
      7 0x10324a bytes_l10324a b_l10324a := by
  have f0 : InstrSpec 0x10324a [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10324a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10324a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10324a (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10324a (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10324a 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x103253 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103253 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103253 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103253 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103253 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103253 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10325c [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10325c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10325c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10325c (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10325c (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10325c 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x103265 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103265 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103265 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103265 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103265 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103265 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10326e [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10326e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10326e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10326e (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10326e (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10326e 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x103277 [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103277 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x103277 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103277 (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103277 (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103277 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x103280 [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103280 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x103280 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103280 (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103280 (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103280 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103253) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10325c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103265) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10326e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103277) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103280) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103289) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l10324a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10324a :=
  Rest.liftedBlock (rest_l10324a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10324a x hx)

theorem rest_l103289 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103289 bytes_l103289) (entryMap (live .l103289))
      20 0x103289 bytes_l103289 b_l103289 := by
  have f0 : InstrSpec 0x103289 [0x4C, 0x89, 0x7C, 0x24, 0x40] (StorePre 0x103289 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x103289 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103289 15 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103289 15 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x103289 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10328e [0x4C, 0x89, 0xBC, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x10328e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10328e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10328e 15 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10328e 15 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x10328e 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103296 [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x103296 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x103296 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103296 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103296 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x103296 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10329b [0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x10329b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10329b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10329b 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10329b 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x10329b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1032a3 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x1032a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1032a3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1032a3 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1032a3 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1032a3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1032a8 [0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x1032a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1032a8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1032a8 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1032a8 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x1032a8 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1032b0 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x1032b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1032b0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1032b0 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1032b0 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1032b0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1032b5 [0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x1032b5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1032b5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1032b5 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1032b5 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x1032b5 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1032bd [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x1032bd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1032bd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1032bd 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1032bd 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1032bd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1032c2 [0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x1032c2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1032c2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1032c2 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1032c2 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x1032c2 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1032ca [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x1032ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1032ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1032ca 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1032ca 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1032ca 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1032cf [0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x1032cf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1032cf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1032cf 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1032cf 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x1032cf 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1032d7 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x1032d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1032d7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1032d7 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1032d7 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1032d7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1032dc [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x1032dc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1032dc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1032dc 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1032dc 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1032dc 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1032e1 [0x48, 0x89, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x1032e1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1032e1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1032e1 1 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1032e1 1 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x1032e1 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1032e9 [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x1032e9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1032e9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1032e9 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1032e9 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x1032e9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x1032f1 [0x48, 0x8D, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1032f1) (leaR64Effect 0x1032f1 6 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1032f1 6 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x1032f1 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1032f9 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1032f9) (movR32Imm32Effect 0x1032f9 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1032f9 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1032f9 0xba (by decide) 0x1) pre_rip
  have f18 : InstrSpec 0x1032fe [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x1032fe) (movR64R64Effect 0x1032fe 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1032fe 7 3).toInstrSpec (mov_r64_r64_effect_step 0x1032fe 0x48 0xdf (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x103301 [0xE8, 0xDA, 0xE5, 0x01, 0x00] (PushPre 0x103301 5) (callEffect (fun _ => 0x1218e0) 0x103306)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103301 0x1218e0 0x103306).toInstrSpec (call_rel32_effect_step 0x103301 0x1e5da (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10328e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103296) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10329b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032a3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032a8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032b0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032b5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032bd) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032c2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032ca) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032cf) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032d7) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032dc) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 70), (1, 72), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032e1) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 70), (1, 72), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032e9) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 70), (1, 72), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032f1) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 70), (1, 72), (3, 3), (4, 4), (5, 5), (6, 76), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032f9) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 70), (1, 72), (2, 78), (3, 3), (4, 4), (5, 5), (6, 76), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032fe) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 70), (1, 72), (2, 78), (3, 3), (4, 4), (5, 5), (6, 76), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103301) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 70), (1, 72), (2, 78), (3, 3), (4, 82), (5, 5), (6, 76), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 84) (by decide) (by decide) rfl rfl

theorem block_l103289 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103289 :=
  Rest.liftedBlock (rest_l103289 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103289 x hx)

theorem rest_l103306_1 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x103306 bytes_l103306) [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      13 0x103358 bytes_l103306_1 b_l103306_1 := by
  have f20 : InstrSpec 0x103358 [0x89, 0xBC, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x103358 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x103358 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x103358 7 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x103358 7 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m32_r32_low_effect_step 0x103358 7 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x10335f [0x44, 0x89, 0x84, 0x24, 0x94, 0x00, 0x00, 0x00] (StorePre 0x10335f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x10335f + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x10335f 8 (.sib 4 none 0 (.d32 0x94)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x10335f 8 (.sib 4 none 0 (.d32 0x94))).toInstrSpec (mov_m32_r32_effect_step 0x10335f 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0x94)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x103367 [0x44, 0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x103367 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x103367 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x103367 9 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x103367 9 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m32_r32_effect_step 0x103367 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x10336f [0x44, 0x89, 0x94, 0x24, 0x9C, 0x00, 0x00, 0x00] (StorePre 0x10336f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x10336f + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x10336f 10 (.sib 4 none 0 (.d32 0x9c)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x10336f 10 (.sib 4 none 0 (.d32 0x9c))).toInstrSpec (mov_m32_r32_effect_step 0x10336f 0x44 (by decide) 2 (.sib 4 none 0 (.d32 0x9c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x103377 [0x48, 0x8D, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103377) (leaR64Effect 0x103377 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103377 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x103377 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x10337f [0x48, 0x8D, 0xB4, 0x24, 0xA0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10337f) (leaR64Effect 0x10337f 6 (.sib 4 none 0 (.d32 0x1a0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10337f 6 (.sib 4 none 0 (.d32 0x1a0))).toInstrSpec (lea_r64_effect_step 0x10337f 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x1a0)) (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x103387 [0xB9, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103387) (movR32Imm32Effect 0x103387 5 1 0xb)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x103387 5 1 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x103387 0xb9 (by decide) 0xb) pre_rip
  have f27 : InstrSpec 0x10338c [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x10338c) (movR64R64Effect 0x10338c 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10338c 7 0).toInstrSpec (mov_r64_r64_effect_step 0x10338c 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10338f [0xF3, 0x48, 0xA5] (RepPre 0x10338f (RepMovsqPre 0x10338f)) (repMovsqEffect 0x10338f)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10338f).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10338f 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f29 : InstrSpec 0x103392 [0x48, 0x8D, 0x5C, 0x24, 0x08] (fun s => s.RIP = 0x103392) (leaR64Effect 0x103392 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x103392 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x103392 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x103397 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x103397) (movR64R64Effect 0x103397 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103397 7 3).toInstrSpec (mov_r64_r64_effect_step 0x103397 0x48 0xdf (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x10339a [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x10339a) (movR64R64Effect 0x10339a 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10339a 6 0).toInstrSpec (mov_r64_r64_effect_step 0x10339a 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10339d [0xE8, 0x6E, 0xC6, 0x00, 0x00] (PushPre 0x10339d 5) (callEffect (fun _ => 0x10fa10) 0x1033a2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10339d 0x10fa10 0x1033a2).toInstrSpec (call_rel32_effect_step 0x10339d 0xc66e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10335f) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103367) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10336f) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103377) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 93), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10337f) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f25 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 93), (1, 59), (2, 63), (4, 4), (5, 5), (6, 95), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103387) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 93), (1, 97), (2, 63), (4, 4), (5, 5), (6, 95), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10338c) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f27 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 93), (1, 97), (2, 63), (4, 4), (5, 5), (6, 95), (7, 99), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10338f) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f28 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 93), (1, 101), (2, 63), (4, 4), (5, 5), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103392) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f29 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 93), (1, 101), (2, 63), (3, 103), (4, 4), (5, 5), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103397) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f30 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 93), (1, 101), (2, 63), (3, 103), (4, 4), (5, 5), (7, 105), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10339a) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f31 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 93), (1, 101), (2, 63), (3, 103), (4, 4), (5, 5), (6, 107), (7, 105), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10339d) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f32 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 93), (1, 101), (2, 63), (3, 103), (4, 109), (5, 5), (6, 107), (7, 105), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa10) f32 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 111) (by decide) (by decide) rfl rfl

theorem rest_l103306 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103306 bytes_l103306) (entryMap (live .l103306))
      33 0x103306 bytes_l103306 b_l103306 := by
  have f0 : InstrSpec 0x103306 [0x8B, 0x44, 0x24, 0x48] (LoadPre 0x103306 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x103306 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x103306 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x103306 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r32_m32_low_effect_step 0x103306 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10330a [0x8B, 0x4C, 0x24, 0x4C] (LoadPre 0x10330a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x10330a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10330a 1 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x10330a 1 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_r32_m32_low_effect_step 0x10330a 1 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10330e [0x0F, 0xC8] (fun s => s.RIP = 0x10330e) (bswapR32Effect 0x10330e 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (bswapR32Effect_footprint 0x10330e 2 0).toInstrSpec (bswap_r32_effect_step 0x10330e 0xc8 (by decide)) pre_rip
  have f3 : InstrSpec 0x103310 [0x0F, 0xC9] (fun s => s.RIP = 0x103310) (bswapR32Effect 0x103310 2 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR32Effect_footprint 0x103310 2 1).toInstrSpec (bswap_r32_effect_step 0x103310 0xc9 (by decide)) pre_rip
  have f4 : InstrSpec 0x103312 [0x8B, 0x54, 0x24, 0x50] (LoadPre 0x103312 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x103312 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x103312 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x103312 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r32_m32_low_effect_step 0x103312 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x103316 [0x0F, 0xCA] (fun s => s.RIP = 0x103316) (bswapR32Effect 0x103316 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR32Effect_footprint 0x103316 2 2).toInstrSpec (bswap_r32_effect_step 0x103316 0xca (by decide)) pre_rip
  have f6 : InstrSpec 0x103318 [0x8B, 0x74, 0x24, 0x54] (LoadPre 0x103318 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x103318 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x103318 6 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x103318 6 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_r32_m32_low_effect_step 0x103318 6 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10331c [0x0F, 0xCE] (fun s => s.RIP = 0x10331c) (bswapR32Effect 0x10331c 2 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (bswapR32Effect_footprint 0x10331c 2 6).toInstrSpec (bswap_r32_effect_step 0x10331c 0xce (by decide)) pre_rip
  have f8 : InstrSpec 0x10331e [0x8B, 0x7C, 0x24, 0x58] (LoadPre 0x10331e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10331e + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10331e 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x10331e 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r32_m32_low_effect_step 0x10331e 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x103322 [0x0F, 0xCF] (fun s => s.RIP = 0x103322) (bswapR32Effect 0x103322 2 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (bswapR32Effect_footprint 0x103322 2 7).toInstrSpec (bswap_r32_effect_step 0x103322 0xcf (by decide)) pre_rip
  have f10 : InstrSpec 0x103324 [0x44, 0x8B, 0x44, 0x24, 0x5C] (LoadPre 0x103324 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x103324 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x103324 8 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x103324 8 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (mov_r32_m32_effect_step 0x103324 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x103329 [0x41, 0x0F, 0xC8] (fun s => s.RIP = 0x103329) (bswapR32Effect 0x103329 3 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (bswapR32Effect_footprint 0x103329 3 8).toInstrSpec (bswap_r32_rex_effect_step 0x103329 0x41 (by decide) 0xc8 (by decide)) pre_rip
  have f12 : InstrSpec 0x10332c [0x44, 0x8B, 0x4C, 0x24, 0x60] (LoadPre 0x10332c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10332c + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x10332c 9 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x10332c 9 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r32_m32_effect_step 0x10332c 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x103331 [0x41, 0x0F, 0xC9] (fun s => s.RIP = 0x103331) (bswapR32Effect 0x103331 3 9)
      [.gpr 9] [] [.reg 9, .rip] :=
    (bswapR32Effect_footprint 0x103331 3 9).toInstrSpec (bswap_r32_rex_effect_step 0x103331 0x41 (by decide) 0xc9 (by decide)) pre_rip
  have f14 : InstrSpec 0x103334 [0x44, 0x8B, 0x54, 0x24, 0x64] (LoadPre 0x103334 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x103334 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x103334 10 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x103334 10 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (mov_r32_m32_effect_step 0x103334 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x103339 [0x41, 0x0F, 0xCA] (fun s => s.RIP = 0x103339) (bswapR32Effect 0x103339 3 10)
      [.gpr 10] [] [.reg 10, .rip] :=
    (bswapR32Effect_footprint 0x103339 3 10).toInstrSpec (bswap_r32_rex_effect_step 0x103339 0x41 (by decide) 0xca (by decide)) pre_rip
  have f16 : InstrSpec 0x10333c [0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x10333c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10333c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x10333c 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10333c 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m32_r32_low_effect_step 0x10333c 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x103343 [0x89, 0x8C, 0x24, 0x84, 0x00, 0x00, 0x00] (StorePre 0x103343 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x103343 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x103343 1 (.sib 4 none 0 (.d32 0x84)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x103343 1 (.sib 4 none 0 (.d32 0x84))).toInstrSpec (mov_m32_r32_low_effect_step 0x103343 1 (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x10334a [0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x10334a 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10334a + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x10334a 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10334a 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m32_r32_low_effect_step 0x10334a 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x103351 [0x89, 0xB4, 0x24, 0x8C, 0x00, 0x00, 0x00] (StorePre 0x103351 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x103351 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x103351 6 (.sib 4 none 0 (.d32 0x8c)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x103351 6 (.sib 4 none 0 (.d32 0x8c))).toInstrSpec (mov_m32_r32_low_effect_step 0x103351 6 (.sib 4 none 0 (.d32 0x8c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10330a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10330e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103310) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103312) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 59), (2, 61), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103316) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103318) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 65), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10331c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10331e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103322) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103324) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 73), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103329) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10332c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 77), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103331) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103334) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103339) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10333c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103343) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10334a) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103351) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103358) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l103306_1 hstride code

theorem block_l103306 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103306 :=
  Rest.liftedBlock (rest_l103306 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103306 x hx)

theorem rest_l1033a2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1033a2 bytes_l1033a2) (entryMap (live .l1033a2))
      6 0x1033a2 bytes_l1033a2 b_l1033a2 := by
  have f0 : InstrSpec 0x1033a2 [0x48, 0x8D, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1033a2) (leaR64Effect 0x1033a2 7 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1033a2 7 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x1033a2 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1033aa [0x48, 0x8D, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1033aa) (leaR64Effect 0x1033aa 2 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1033aa 2 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (lea_r64_effect_step 0x1033aa 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1033b2 [0x4C, 0x8D, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1033b2) (leaR64Effect 0x1033b2 8 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x1033b2 8 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (lea_r64_effect_step 0x1033b2 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1033ba [0xB9, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1033ba) (movR32Imm32Effect 0x1033ba 5 1 0x20)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1033ba 5 1 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x1033ba 0xb9 (by decide) 0x20) pre_rip
  have f4 : InstrSpec 0x1033bf [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x1033bf) (movR64R64Effect 0x1033bf 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1033bf 6 3).toInstrSpec (mov_r64_r64_effect_step 0x1033bf 0x48 0xde (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1033c2 [0xE8, 0x59, 0x1B, 0x00, 0x00] (PushPre 0x1033c2 5) (callEffect (fun _ => 0x104f20) 0x1033c7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1033c2 0x104f20 0x1033c7).toInstrSpec (call_rel32_effect_step 0x1033c2 0x1b59 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033aa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033b2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033ba) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 59), (2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033bf) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 59), (2, 55), (3, 3), (4, 4), (5, 5), (6, 61), (7, 53), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033c2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 59), (2, 55), (3, 3), (4, 63), (5, 5), (6, 61), (7, 53), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f20) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l1033a2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1033a2 :=
  Rest.liftedBlock (rest_l1033a2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1033a2 x hx)

theorem rest_l1033c7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1033c7 bytes_l1033c7) (entryMap (live .l1033c7))
      3 0x1033c7 bytes_l1033c7 b_l1033c7 := by
  have f0 : InstrSpec 0x1033c7 [0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x1033c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1033c7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1033c7 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1033c7 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x1033c7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1033cf [0x48, 0x85, 0xC0] (fun s => s.RIP = 0x1033cf) (testR64R64Effect 0x1033cf 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1033cf 0 0).toInstrSpec (test_r64_r64_effect_step 0x1033cf 0x48 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033cf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033d2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1033d2 4 0x25) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1033c7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1033c7 :=
  Rest.liftedBlock (rest_l1033c7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1033c7 x hx)

theorem rest_l1033d4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1033d4 bytes_l1033d4) (entryMap (live .l1033d4))
      3 0x1033d4 bytes_l1033d4 b_l1033d4 := by
  have f0 : InstrSpec 0x1033d4 [0x48, 0x8B, 0xBC, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x1033d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1033d4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1033d4 7 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1033d4 7 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x1033d4 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1033dc [0x48, 0x85, 0xFF] (fun s => s.RIP = 0x1033dc) (testR64R64Effect 0x1033dc 7 7)
      [.gpr 7, .gpr 7] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1033dc 7 7).toInstrSpec (test_r64_r64_effect_step 0x1033dc 0x48 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033dc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033df) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1033df 4 0x18) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1033d4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1033d4 :=
  Rest.liftedBlock (rest_l1033d4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1033d4 x hx)

theorem rest_l1033e1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1033e1 bytes_l1033e1) (entryMap (live .l1033e1))
      4 0x1033e1 bytes_l1033e1 b_l1033e1 := by
  have f0 : InstrSpec 0x1033e1 [0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x1033e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1033e1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1033e1 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1033e1 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x1033e1 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1033e9 [0x48, 0x8B, 0x09] (LoadPre 0x1033e9 (fun s => AddrMode.addr (.base 1 .none) s (0x1033e9 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1033e9 1 (.base 1 .none))
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1033e9 1 (.base 1 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1033e9 0x48 (by decide) 1 (.base 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1033ec [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x1033ec) (testR64R64Effect 0x1033ec 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1033ec 1 1).toInstrSpec (test_r64_r64_effect_step 0x1033ec 0x48 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033e9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033ec) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033ef) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x1033ef 4 0x8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1033e1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1033e1 :=
  Rest.liftedBlock (rest_l1033e1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1033e1 x hx)

theorem rest_l1033f1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1033f1 bytes_l1033f1) (entryMap (live .l1033f1))
      1 0x1033f1 bytes_l1033f1 b_l1033f1 := by
  have f0 : InstrSpec 0x1033f1 [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x1033f1) (movR64R64Effect 0x1033f1 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1033f1 3 0).toInstrSpec (mov_r64_r64_effect_step 0x1033f1 0x48 0xc3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0)]) (p' := 0x1033f4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l1033f1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1033f1 :=
  Rest.liftedBlock (rest_l1033f1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1033f1 x hx)

theorem rest_l1033f6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1033f6 bytes_l1033f6) (entryMap (live .l1033f6))
      1 0x1033f6 bytes_l1033f6 b_l1033f6 := by
  have f0 : InstrSpec 0x1033f6 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1033f6) (movR64R64Effect 0x1033f6 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1033f6 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1033f6 0x48 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033f9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1033f6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1033f6 :=
  Rest.liftedBlock (rest_l1033f6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1033f6 x hx)

theorem rest_l1033f9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1033f9 bytes_l1033f9) (entryMap (live .l1033f9))
      6 0x1033f9 bytes_l1033f9 b_l1033f9 := by
  have f0 : InstrSpec 0x1033f9 [0x48, 0x81, 0xC4, 0xF8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1033f9) (addR64Imm32Effect 0x1033f9 4 0x1f8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x1033f9 4 0x1f8).toInstrSpec (add_r64_imm32_effect_step 0x1033f9 0x48 0xc4 0x1f8 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103400 [0x5B] (PopPre 0x103400) (popR64Effect 0x103400 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103400 1 3).toInstrSpec (pop_r64_effect_step 0x103400 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x103401 [0x41, 0x5C] (PopPre 0x103401) (popR64Effect 0x103401 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103401 2 12).toInstrSpec (pop_r64_rex_effect_step 0x103401 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x103403 [0x41, 0x5E] (PopPre 0x103403) (popR64Effect 0x103403 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103403 2 14).toInstrSpec (pop_r64_rex_effect_step 0x103403 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x103405 [0x41, 0x5F] (PopPre 0x103405) (popR64Effect 0x103405 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103405 2 15).toInstrSpec (pop_r64_rex_effect_step 0x103405 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x103407 [0xC3] (RetPre 0x103407) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x103407).toInstrSpec (ret_effect_step 0x103407) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103400) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103401) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103403) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103405) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (14, 61), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103407) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (14, 61), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l1033f9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1033f9 :=
  Rest.liftedBlock (rest_l1033f9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1033f9 x hx)

theorem rest_l103408 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103408 bytes_l103408) (entryMap (live .l103408))
      4 0x103408 bytes_l103408 b_l103408 := by
  have f0 : InstrSpec 0x103408 [0x48, 0xC7, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103408 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x103408 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103408 (.sib 4 none 0 (.d32 0x100)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103408 (.sib 4 none 0 (.d32 0x100)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103408 0x48 (by decide) (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x103414 [0x48, 0xC7, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (StorePre 0x103414 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x103414 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103414 (.sib 4 none 0 (.d32 0xf8)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103414 (.sib 4 none 0 (.d32 0xf8)) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x103414 0x48 (by decide) (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103420 [0x48, 0x8D, 0xBC, 0x24, 0xF8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103420) (leaR64Effect 0x103420 7 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103420 7 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (lea_r64_effect_step 0x103420 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103428 [0xE8, 0x13, 0xCE, 0xFF, 0xFF] (PushPre 0x103428 5) (callEffect (fun _ => 0x100240) 0x10342d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103428 0x100240 0x10342d).toInstrSpec (call_rel32_effect_step 0x103428 0xffffce13 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103414) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103420) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103428) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100240) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l103408 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103408 :=
  Rest.liftedBlock (rest_l103408 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103408 x hx)

theorem rest_l10342d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10342d bytes_l10342d) (entryMap (live .l10342d))
      1 0x10342d bytes_l10342d b_l10342d := by
  have f0 : InstrSpec 0x10342d [0xE8, 0xFE, 0xD5, 0xFF, 0xFF] (PushPre 0x10342d 5) (callEffect (fun _ => 0x100a30) 0x103432)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10342d 0x100a30 0x103432).toInstrSpec (call_rel32_effect_step 0x10342d 0xffffd5fe (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := []) (p' := 0x100a30) f0 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 54) (by decide) (by decide) rfl rfl

theorem block_l10342d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10342d :=
  Rest.liftedBlock (rest_l10342d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10342d x hx)

theorem rest_l103432 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103432 bytes_l103432) (entryMap (live .l103432))
      2 0x103432 bytes_l103432 b_l103432 := by
  have f0 : InstrSpec 0x103432 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x103432) (leaR64Effect 0x103432 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103432 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x103432 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103437 [0xE8, 0x44, 0xCD, 0xFF, 0xFF] (PushPre 0x103437 5) (callEffect (fun _ => 0x100180) 0x10343c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103437 0x100180 0x10343c).toInstrSpec (call_rel32_effect_step 0x103437 0xffffcd44 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103437) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100180) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l103432 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103432 :=
  Rest.liftedBlock (rest_l103432 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103432 x hx)

theorem rest_l10343c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10343c bytes_l10343c) (entryMap (live .l10343c))
      1 0x10343c bytes_l10343c b_l10343c := by
  have f0 : InstrSpec 0x10343c [0xE8, 0xEF, 0xD5, 0xFF, 0xFF] (PushPre 0x10343c 5) (callEffect (fun _ => 0x100a30) 0x103441)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10343c 0x100a30 0x103441).toInstrSpec (call_rel32_effect_step 0x10343c 0xffffd5ef (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := []) (p' := 0x100a30) f0 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 54) (by decide) (by decide) rfl rfl

theorem block_l10343c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10343c :=
  Rest.liftedBlock (rest_l10343c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10343c x hx)

theorem rest_l103441 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103441 bytes_l103441) (entryMap (live .l103441))
      2 0x103441 bytes_l103441 b_l103441 := by
  have f0 : InstrSpec 0x103441 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103441) (fun _ => nopEffect 0x103441 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x103441 10).toInstrSpec (nop_m_effect_step 0x103441 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10344b [0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x10344b) (fun _ => nopEffect 0x10344b 5)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10344b 5).toInstrSpec (nop_m_effect_step 0x10344b [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10344b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103450) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l103441 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103441 :=
  Rest.liftedBlock (rest_l103441 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103441 x hx)

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

theorem_by block_l102630_eval :
    program.runBlock (dialect code) ⟨.l102630, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102651_eval :
    program.runBlock (dialect code) ⟨.l102651, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10265c_eval :
    program.runBlock (dialect code) ⟨.l10265c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102696_eval :
    program.runBlock (dialect code) ⟨.l102696, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1026a6_eval :
    program.runBlock (dialect code) ⟨.l1026a6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102795_eval :
    program.runBlock (dialect code) ⟨.l102795, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10279c_eval :
    program.runBlock (dialect code) ⟨.l10279c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1027a6_eval :
    program.runBlock (dialect code) ⟨.l1027a6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1027b3_eval :
    program.runBlock (dialect code) ⟨.l1027b3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1027b5_eval :
    program.runBlock (dialect code) ⟨.l1027b5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1027b7_eval :
    program.runBlock (dialect code) ⟨.l1027b7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10281c_eval :
    program.runBlock (dialect code) ⟨.l10281c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102883_eval :
    program.runBlock (dialect code) ⟨.l102883, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10289f_eval :
    program.runBlock (dialect code) ⟨.l10289f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1028a4_eval :
    program.runBlock (dialect code) ⟨.l1028a4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1028d6_eval :
    program.runBlock (dialect code) ⟨.l1028d6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1028e0_eval :
    program.runBlock (dialect code) ⟨.l1028e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10294f_eval :
    program.runBlock (dialect code) ⟨.l10294f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1029bf_eval :
    program.runBlock (dialect code) ⟨.l1029bf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1029cb_eval :
    program.runBlock (dialect code) ⟨.l1029cb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1029d6_eval :
    program.runBlock (dialect code) ⟨.l1029d6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102a86_eval :
    program.runBlock (dialect code) ⟨.l102a86, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102a92_eval :
    program.runBlock (dialect code) ⟨.l102a92, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102a9d_eval :
    program.runBlock (dialect code) ⟨.l102a9d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102b4a_eval :
    program.runBlock (dialect code) ⟨.l102b4a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102b52_eval :
    program.runBlock (dialect code) ⟨.l102b52, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102b95_eval :
    program.runBlock (dialect code) ⟨.l102b95, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102b9b_eval :
    program.runBlock (dialect code) ⟨.l102b9b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102bb0_eval :
    program.runBlock (dialect code) ⟨.l102bb0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102bb5_eval :
    program.runBlock (dialect code) ⟨.l102bb5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102bcd_eval :
    program.runBlock (dialect code) ⟨.l102bcd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102c28_eval :
    program.runBlock (dialect code) ⟨.l102c28, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102c30_eval :
    program.runBlock (dialect code) ⟨.l102c30, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102ca2_eval :
    program.runBlock (dialect code) ⟨.l102ca2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102cdb_eval :
    program.runBlock (dialect code) ⟨.l102cdb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102ce8_eval :
    program.runBlock (dialect code) ⟨.l102ce8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102cfb_eval :
    program.runBlock (dialect code) ⟨.l102cfb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102d06_eval :
    program.runBlock (dialect code) ⟨.l102d06, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102d49_eval :
    program.runBlock (dialect code) ⟨.l102d49, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102d59_eval :
    program.runBlock (dialect code) ⟨.l102d59, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102d6d_eval :
    program.runBlock (dialect code) ⟨.l102d6d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102dce_eval :
    program.runBlock (dialect code) ⟨.l102dce, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102de1_eval :
    program.runBlock (dialect code) ⟨.l102de1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102e01_eval :
    program.runBlock (dialect code) ⟨.l102e01, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102e1f_eval :
    program.runBlock (dialect code) ⟨.l102e1f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102e32_eval :
    program.runBlock (dialect code) ⟨.l102e32, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102e56_eval :
    program.runBlock (dialect code) ⟨.l102e56, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102e5e_eval :
    program.runBlock (dialect code) ⟨.l102e5e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102e62_eval :
    program.runBlock (dialect code) ⟨.l102e62, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102e67_eval :
    program.runBlock (dialect code) ⟨.l102e67, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102e77_eval :
    program.runBlock (dialect code) ⟨.l102e77, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102ec2_eval :
    program.runBlock (dialect code) ⟨.l102ec2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102ed9_eval :
    program.runBlock (dialect code) ⟨.l102ed9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102f0b_eval :
    program.runBlock (dialect code) ⟨.l102f0b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102f24_eval :
    program.runBlock (dialect code) ⟨.l102f24, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102f2b_eval :
    program.runBlock (dialect code) ⟨.l102f2b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102f2e_eval :
    program.runBlock (dialect code) ⟨.l102f2e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102f45_eval :
    program.runBlock (dialect code) ⟨.l102f45, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102f60_eval :
    program.runBlock (dialect code) ⟨.l102f60, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102f79_eval :
    program.runBlock (dialect code) ⟨.l102f79, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102f9d_eval :
    program.runBlock (dialect code) ⟨.l102f9d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102fa7_eval :
    program.runBlock (dialect code) ⟨.l102fa7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102faf_eval :
    program.runBlock (dialect code) ⟨.l102faf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102fb4_eval :
    program.runBlock (dialect code) ⟨.l102fb4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102fe9_eval :
    program.runBlock (dialect code) ⟨.l102fe9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102ff4_eval :
    program.runBlock (dialect code) ⟨.l102ff4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10302c_eval :
    program.runBlock (dialect code) ⟨.l10302c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103037_eval :
    program.runBlock (dialect code) ⟨.l103037, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103101_eval :
    program.runBlock (dialect code) ⟨.l103101, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103115_eval :
    program.runBlock (dialect code) ⟨.l103115, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10311e_eval :
    program.runBlock (dialect code) ⟨.l10311e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103154_eval :
    program.runBlock (dialect code) ⟨.l103154, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103170_eval :
    program.runBlock (dialect code) ⟨.l103170, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1031c3_eval :
    program.runBlock (dialect code) ⟨.l1031c3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1031cd_eval :
    program.runBlock (dialect code) ⟨.l1031cd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10324a_eval :
    program.runBlock (dialect code) ⟨.l10324a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103289_eval :
    program.runBlock (dialect code) ⟨.l103289, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103306_eval :
    program.runBlock (dialect code) ⟨.l103306, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1033a2_eval :
    program.runBlock (dialect code) ⟨.l1033a2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1033c7_eval :
    program.runBlock (dialect code) ⟨.l1033c7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1033d4_eval :
    program.runBlock (dialect code) ⟨.l1033d4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1033e1_eval :
    program.runBlock (dialect code) ⟨.l1033e1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1033f1_eval :
    program.runBlock (dialect code) ⟨.l1033f1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1033f6_eval :
    program.runBlock (dialect code) ⟨.l1033f6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1033f9_eval :
    program.runBlock (dialect code) ⟨.l1033f9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103408_eval :
    program.runBlock (dialect code) ⟨.l103408, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10342d_eval :
    program.runBlock (dialect code) ⟨.l10342d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103432_eval :
    program.runBlock (dialect code) ⟨.l103432, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10343c_eval :
    program.runBlock (dialect code) ⟨.l10343c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103441_eval :
    program.runBlock (dialect code) ⟨.l103441, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
