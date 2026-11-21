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

theorem rest_l12873d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12873d bytes_l12873d) (entryMap (live .l12873d))
      16 0x12873d bytes_l12873d b_l12873d := by
  have f0 : InstrSpec 0x12873d [0x55] (PushPre 0x12873d 1) (pushR64Effect 0x12873d 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12873d 1 5).toInstrSpec (push_r64_effect_step 0x12873d 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x12873e [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x12873e) (movR64R64Effect 0x12873e 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x12873e 5 4).toInstrSpec (mov_r64_r64_effect_step 0x12873e 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128741 [0x48, 0x83, 0xEC, 0x10] (fun s => s.RIP = 0x128741) (subR64Imm8Effect 0x128741 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x128741 4 0x10).toInstrSpec (sub_r64_imm8_effect_step 0x128741 0x48 0xec 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x128745 [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x128745) (movR64R64Effect 0x128745 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x128745 0 9).toInstrSpec (mov_r64_r64_effect_step 0x128745 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x128748 [0x4D, 0x89, 0xC2] (fun s => s.RIP = 0x128748) (movR64R64Effect 0x128748 10 8)
      [.gpr 8] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x128748 10 8).toInstrSpec (mov_r64_r64_effect_step 0x128748 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12874b [0x49, 0x89, 0xC9] (fun s => s.RIP = 0x12874b) (movR64R64Effect 0x12874b 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x12874b 9 1).toInstrSpec (mov_r64_r64_effect_step 0x12874b 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12874e [0x4C, 0x8D, 0x45, 0xF8] (fun s => s.RIP = 0x12874e) (leaR64Effect 0x12874e 8 (.base 5 (.d8 0xf8)))
      [.gpr 5] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x12874e 8 (.base 5 (.d8 0xf8))).toInstrSpec (lea_r64_effect_step 0x12874e 0x4c (by decide) 0 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x128752 [0x49, 0x89, 0x30] (StorePre 0x128752 3 (fun s => AddrMode.addr (.base 8 .none) s (0x128752 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x128752 6 (.base 8 .none))
      [.gpr 6, .gpr 8] [] [.rip] :=
    (movM64R64Effect_footprint 0x128752 6 (.base 8 .none)).toInstrSpec (mov_m64_r64_effect_step 0x128752 0x49 (by decide) 6 (.base 8 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x128755 [0x48, 0x8D, 0x4D, 0xF0] (fun s => s.RIP = 0x128755) (leaR64Effect 0x128755 1 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x128755 1 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x128755 0x48 (by decide) 1 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x128759 [0x48, 0x89, 0x11] (StorePre 0x128759 3 (fun s => AddrMode.addr (.base 1 .none) s (0x128759 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x128759 2 (.base 1 .none))
      [.gpr 2, .gpr 1] [] [.rip] :=
    (movM64R64Effect_footprint 0x128759 2 (.base 1 .none)).toInstrSpec (mov_m64_r64_effect_step 0x128759 0x48 (by decide) 2 (.base 1 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x12875c [0x48, 0x8D, 0x15, 0x05, 0xB6, 0x0D, 0x00] (fun s => s.RIP = 0x12875c) (leaR64Effect 0x12875c 2 (.rip 0xdb605))
      [] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x12875c 2 (.rip 0xdb605)).toInstrSpec (lea_r64_effect_step 0x12875c 0x48 (by decide) 2 (.rip 0xdb605) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x128763 [0x4C, 0x89, 0xC6] (fun s => s.RIP = 0x128763) (movR64R64Effect 0x128763 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x128763 6 8).toInstrSpec (mov_r64_r64_effect_step 0x128763 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x128766 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x128766) (movR64R64Effect 0x128766 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x128766 8 2).toInstrSpec (mov_r64_r64_effect_step 0x128766 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x128769 [0x50] (PushPre 0x128769 1) (pushR64Effect 0x128769 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128769 1 0).toInstrSpec (push_r64_effect_step 0x128769 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f14 : InstrSpec 0x12876a [0x41, 0x52] (PushPre 0x12876a 2) (pushR64Effect 0x12876a 2 10)
      [.gpr 4, .gpr 10] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12876a 2 10).toInstrSpec (push_r64_rex_effect_step 0x12876a 0x41 0x52 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f15 : InstrSpec 0x12876c [0xFF, 0x15, 0x56, 0xB6, 0x0D, 0x00] (GoesTo (CallMemPre 0x12876c (.rip 0xdb656)) (callEffect (callMemPtr 0x12876c (.rip 0xdb656)) (0x12876c + BitVec.ofNat 64 (callMemLen (.rip 0xdb656)))) 0x12965d) (callEffect (callMemPtr 0x12876c (.rip 0xdb656)) (0x12876c + BitVec.ofNat 64 (callMemLen (.rip 0xdb656))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x12876c (.rip 0xdb656)).toInstrSpec (call_m64_effect_step 0x12876c (.rip 0xdb656) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12965d
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x12873e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (4, 53), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x128741) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x128745) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x128748) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61)]) (p' := 0x12874b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 63), (10, 61)]) (p' := 0x12874e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 65), (9, 63), (10, 61)]) (p' := 0x128752) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 59), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 65), (9, 63), (10, 61)]) (p' := 0x128755) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 65), (9, 63), (10, 61)]) (p' := 0x128759) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 65), (9, 63), (10, 61)]) (p' := 0x12875c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 68), (2, 71), (4, 57), (5, 55), (6, 6), (7, 7), (8, 65), (9, 63), (10, 61)]) (p' := 0x128763) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 59), (1, 68), (2, 71), (4, 57), (5, 55), (6, 73), (7, 7), (8, 65), (9, 63), (10, 61)]) (p' := 0x128766) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 59), (1, 68), (2, 71), (4, 57), (5, 55), (6, 73), (7, 7), (8, 75), (9, 63), (10, 61)]) (p' := 0x128769) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 59), (1, 68), (2, 71), (4, 77), (5, 55), (6, 73), (7, 7), (8, 75), (9, 63), (10, 61)]) (p' := 0x12876a) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 59), (1, 68), (2, 71), (4, 79), (5, 55), (6, 73), (7, 7), (8, 75), (9, 63), (10, 61)]) (p' := 0x12876c) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 59), (1, 68), (2, 71), (4, 81), (5, 55), (6, 73), (7, 7), (8, 75), (9, 63), (10, 61)]) (p' := 0x12965d) f15 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 83) (by decide) (by decide) rfl rfl

theorem block_l12873d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12873d :=
  Rest.liftedBlock (rest_l12873d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12873d x hx)

theorem rest_l128772 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128772 bytes_l128772) (entryMap (live .l128772))
      14 0x128772 bytes_l128772 b_l128772 := by
  have f0 : InstrSpec 0x128772 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128772) (fun _ => nopEffect 0x128772 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x128772 10).toInstrSpec (nop_m_effect_step 0x128772 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12877c [0x0F, 0x1F, 0x40, 0x00] (fun s => s.RIP = 0x12877c) (fun _ => nopEffect 0x12877c 4)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12877c 4).toInstrSpec (nop_m_effect_step 0x12877c [] (by decide) (by decide) (.base 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128780 [0x55] (PushPre 0x128780 1) (pushR64Effect 0x128780 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128780 1 5).toInstrSpec (push_r64_effect_step 0x128780 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x128781 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x128781) (movR64R64Effect 0x128781 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x128781 5 4).toInstrSpec (mov_r64_r64_effect_step 0x128781 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x128784 [0x41, 0x57] (PushPre 0x128784 2) (pushR64Effect 0x128784 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128784 2 15).toInstrSpec (push_r64_rex_effect_step 0x128784 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x128786 [0x41, 0x56] (PushPre 0x128786 2) (pushR64Effect 0x128786 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128786 2 14).toInstrSpec (push_r64_rex_effect_step 0x128786 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x128788 [0x41, 0x55] (PushPre 0x128788 2) (pushR64Effect 0x128788 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128788 2 13).toInstrSpec (push_r64_rex_effect_step 0x128788 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x12878a [0x41, 0x54] (PushPre 0x12878a 2) (pushR64Effect 0x12878a 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12878a 2 12).toInstrSpec (push_r64_rex_effect_step 0x12878a 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x12878c [0x53] (PushPre 0x12878c 1) (pushR64Effect 0x12878c 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12878c 1 3).toInstrSpec (push_r64_effect_step 0x12878c 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x12878d [0x48, 0x83, 0xEC, 0x48] (fun s => s.RIP = 0x12878d) (subR64Imm8Effect 0x12878d 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x12878d 4 0x48).toInstrSpec (sub_r64_imm8_effect_step 0x12878d 0x48 0xec 0x48 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x128791 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x128791) (movR64R64Effect 0x128791 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x128791 3 7).toInstrSpec (mov_r64_r64_effect_step 0x128791 0x48 0xfb (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x128794 [0x41, 0xB4, 0x01] (fun s => s.RIP = 0x128794) (movR8Imm8Effect 0x128794 3 12 0x1)
      [.gpr 12] [] [.reg 12, .rip] :=
    (movR8Imm8Effect_footprint 0x128794 3 12 0x1).toInstrSpec (mov_r8_imm8_rex_effect_step 0x128794 0x41 (by decide) 0xb4 (by decide) 0x1) pre_rip
  have f12 : InstrSpec 0x128797 [0x80, 0x7F, 0x08, 0x00] (LoadPre 0x128797 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x128797 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x128797 4 (.base 7 (.d8 0x8)) 0x0)
      [.gpr 7] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x128797 4 (.base 7 (.d8 0x8)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x128797 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12877c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128780) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128781) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128784) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128786) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128788) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12878a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12878c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12878d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 69), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128791) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 71), (4, 69), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128794) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 71), (4, 69), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 73), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128797) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 2), (3, 71), (4, 69), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 73), (13, 13), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12879b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 77) (jcc_rel8_effect_step 0x12879b 4 0x1a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128772 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128772 :=
  Rest.liftedBlock (rest_l128772 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128772 x hx)

theorem rest_l12879d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12879d bytes_l12879d) (entryMap (live .l12879d))
      11 0x12879d bytes_l12879d b_l12879d := by
  have f0 : InstrSpec 0x12879d [0x44, 0x88, 0x63, 0x08] (StorePre 0x12879d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12879d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x12879d 4 12 (.base 3 (.d8 0x8)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x12879d 4 12 (.base 3 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x12879d 0x44 (by decide) 4 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1287a1 [0xC6, 0x43, 0x09, 0x01] (StorePre 0x1287a1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x9)) s (0x1287a1 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1287a1 (.base 3 (.d8 0x9)) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1287a1 (.base 3 (.d8 0x9)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x1287a1 (.base 3 (.d8 0x9)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1287a5 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1287a5) (movR64R64Effect 0x1287a5 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1287a5 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1287a5 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1287a8 [0x48, 0x83, 0xC4, 0x48] (fun s => s.RIP = 0x1287a8) (addR64Imm8Effect 0x1287a8 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1287a8 4 0x48).toInstrSpec (add_r64_imm8_effect_step 0x1287a8 0x48 0xc4 0x48 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1287ac [0x5B] (PopPre 0x1287ac) (popR64Effect 0x1287ac 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1287ac 1 3).toInstrSpec (pop_r64_effect_step 0x1287ac 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1287ad [0x41, 0x5C] (PopPre 0x1287ad) (popR64Effect 0x1287ad 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1287ad 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1287ad 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1287af [0x41, 0x5D] (PopPre 0x1287af) (popR64Effect 0x1287af 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1287af 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1287af 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1287b1 [0x41, 0x5E] (PopPre 0x1287b1) (popR64Effect 0x1287b1 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1287b1 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1287b1 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x1287b3 [0x41, 0x5F] (PopPre 0x1287b3) (popR64Effect 0x1287b3 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1287b3 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1287b3 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x1287b5 [0x5D] (PopPre 0x1287b5) (popR64Effect 0x1287b5 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1287b5 1 5).toInstrSpec (pop_r64_effect_step 0x1287b5 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x1287b6 [0xC3] (RetPre 0x1287b6) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1287b6).toInstrSpec (ret_effect_step 0x1287b6) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1287a1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1287a5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1287a8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1287ac) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 59), (4, 60), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1287ad) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 59), (4, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1287af) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 59), (4, 66), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 62), (13, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1287b1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 59), (4, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 62), (13, 65), (14, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1287b3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 59), (4, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 62), (13, 65), (14, 68), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1287b5) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f9 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 75) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 76) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 59), (4, 75), (5, 74), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 62), (13, 65), (14, 68), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1287b6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f10 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 78) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 79) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 59), (4, 78), (5, 74), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 62), (13, 65), (14, 68), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) f10 (by decide) rfl rfl rfl (by decide)

theorem block_l12879d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12879d :=
  Rest.liftedBlock (rest_l12879d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12879d x hx)

theorem rest_l1287b7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1287b7 bytes_l1287b7) (entryMap (live .l1287b7))
      6 0x1287b7 bytes_l1287b7 b_l1287b7 := by
  have f0 : InstrSpec 0x1287b7 [0x48, 0x89, 0x4D, 0xC0] (StorePre 0x1287b7 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x1287b7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1287b7 1 (.base 5 (.d8 0xc0)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1287b7 1 (.base 5 (.d8 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x1287b7 0x48 (by decide) 1 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1287bb [0x4C, 0x89, 0x45, 0xC8] (StorePre 0x1287bb 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x1287bb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1287bb 8 (.base 5 (.d8 0xc8)))
      [.gpr 8, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1287bb 8 (.base 5 (.d8 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x1287bb 0x4c (by decide) 0 (.base 5 (.d8 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1287bf [0x4C, 0x8B, 0x3B] (LoadPre 0x1287bf (fun s => AddrMode.addr (.base 3 .none) s (0x1287bf + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1287bf 15 (.base 3 .none))
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x1287bf 15 (.base 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1287bf 0x4c (by decide) 7 (.base 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1287c2 [0x41, 0xF6, 0x47, 0x12, 0x80] (LoadPre 0x1287c2 (fun s => AddrMode.addr (.base 15 (.d8 0x12)) s (0x1287c2 + BitVec.ofNat 64 5)) 1) (testM8Imm8Effect 0x1287c2 5 (.base 15 (.d8 0x12)) 0x80)
      [.gpr 15] [] [.flags, .rip] :=
    (testM8Imm8Effect_footprint 0x1287c2 5 (.base 15 (.d8 0x12)) 0x80).toInstrSpec (test_m8_imm8_rex_effect_step 0x1287c2 0x41 (by decide) (.base 15 (.d8 0x12)) (by decide) (by decide) (by decide) 0x80) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1287c7 [0x0F, 0xB6, 0x43, 0x09] (LoadPre 0x1287c7 (fun s => AddrMode.addr (.base 3 (.d8 0x9)) s (0x1287c7 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1287c7 4 0 (.base 3 (.d8 0x9)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1287c7 4 0 (.base 3 (.d8 0x9))).toInstrSpec (movzx_r32_m8_effect_step 0x1287c7 0 (.base 3 (.d8 0x9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1287bb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1287bf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1287c2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1287c7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1287cb) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x1287cb 5 0x74) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1287b7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1287b7 :=
  Rest.liftedBlock (rest_l1287b7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1287b7 x hx)

theorem rest_l1287cd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1287cd bytes_l1287cd) (entryMap (live .l1287cd))
      10 0x1287cd bytes_l1287cd b_l1287cd := by
  have f0 : InstrSpec 0x1287cd [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x1287cd) (movR64R64Effect 0x1287cd 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1287cd 14 6).toInstrSpec (mov_r64_r64_effect_step 0x1287cd 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1287d0 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x1287d0) (movR64R64Effect 0x1287d0 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1287d0 13 2).toInstrSpec (mov_r64_r64_effect_step 0x1287d0 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1287d3 [0x0F, 0xB6, 0xD0] (fun s => s.RIP = 0x1287d3) (movzxR32R8Effect 0x1287d3 3 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x1287d3 3 2 0).toInstrSpec (movzx_r32_r8_effect_step 0x1287d3 0xd0 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1287d6 [0x48, 0x83, 0xF2, 0x03] (fun s => s.RIP = 0x1287d6) (xorR64Imm8Effect 0x1287d6 2 0x3)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR64Imm8Effect_footprint 0x1287d6 2 0x3).toInstrSpec (xor_r64_imm8_effect_step 0x1287d6 0x48 0xf2 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1287da [0x48, 0x8D, 0x0D, 0x46, 0xB4, 0x0D, 0x00] (fun s => s.RIP = 0x1287da) (leaR64Effect 0x1287da 1 (.rip 0xdb446))
      [] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x1287da 1 (.rip 0xdb446)).toInstrSpec (lea_r64_effect_step 0x1287da 0x48 (by decide) 1 (.rip 0xdb446) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1287e1 [0x48, 0x8D, 0x35, 0x3C, 0xB4, 0x0D, 0x00] (fun s => s.RIP = 0x1287e1) (leaR64Effect 0x1287e1 6 (.rip 0xdb43c))
      [] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1287e1 6 (.rip 0xdb43c)).toInstrSpec (lea_r64_effect_step 0x1287e1 0x48 (by decide) 6 (.rip 0xdb43c) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1287e8 [0x84, 0xC0] (fun s => s.RIP = 0x1287e8) (testR8R8Effect 0x1287e8 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1287e8 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x1287e8 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1287ea [0x48, 0x0F, 0x45, 0xF1] (fun s => s.RIP = 0x1287ea) (atFlags (condHolds 5) (cmovR64R64Effect 0x1287ea 4 6 1))
      [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 6, .rip] :=
    (cmovR64R64Effect_footprint 0x1287ea 4 6 1 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x1287ea 5 0x48 (by decide) 0xf1 (by decide) c)) pre_rip
  have f8 : InstrSpec 0x1287ee [0x49, 0x8B, 0x3F] (LoadPre 0x1287ee (fun s => AddrMode.addr (.base 15 .none) s (0x1287ee + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1287ee 7 (.base 15 .none))
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1287ee 7 (.base 15 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1287ee 0x49 (by decide) 7 (.base 15 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1287f1 [0x49, 0x8B, 0x47, 0x08] (LoadPre 0x1287f1 (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x1287f1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1287f1 0 (.base 15 (.d8 0x8)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1287f1 0 (.base 15 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1287f1 0x49 (by decide) 0 (.base 15 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (6, 6), (15, 15)]) (p' := 0x1287d0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (6, 6), (15, 15)]) (p' := 0x1287d3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 55), (6, 6), (15, 15)]) (p' := 0x1287d6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (6, 6), (15, 15)]) (p' := 0x1287da) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 58), (6, 6), (15, 15)]) (p' := 0x1287e1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 58), (6, 60), (15, 15)]) (p' := 0x1287e8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 58), (6, 60), (15, 15), (19, 62)]) (p' := 0x1287ea) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 58), (15, 15), (19, 62)]) (p' := 0x1287ee) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 58), (15, 15), (19, 62)]) (p' := 0x1287f1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(1, 58), (15, 15), (19, 62)]) (p' := 0x1287f5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l1287cd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1287cd :=
  Rest.liftedBlock (rest_l1287cd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1287cd x hx)

theorem rest_l1287f8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1287f8 bytes_l1287f8) (entryMap (live .l1287f8))
      2 0x1287f8 bytes_l1287f8 b_l1287f8 := by
  have f0 : InstrSpec 0x1287f8 [0x84, 0xC0] (fun s => s.RIP = 0x1287f8) (testR8R8Effect 0x1287f8 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1287f8 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x1287f8 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1287fa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1287fa 5 0xa1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1287f8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1287f8 :=
  Rest.liftedBlock (rest_l1287f8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1287f8 x hx)

theorem rest_l1287fc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1287fc bytes_l1287fc) (entryMap (live .l1287fc))
      4 0x1287fc bytes_l1287fc b_l1287fc := by
  have f0 : InstrSpec 0x1287fc [0x49, 0x8B, 0x3F] (LoadPre 0x1287fc (fun s => AddrMode.addr (.base 15 .none) s (0x1287fc + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1287fc 7 (.base 15 .none))
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1287fc 7 (.base 15 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1287fc 0x49 (by decide) 7 (.base 15 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1287ff [0x49, 0x8B, 0x47, 0x08] (LoadPre 0x1287ff (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x1287ff + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1287ff 0 (.base 15 (.d8 0x8)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1287ff 0 (.base 15 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1287ff 0x49 (by decide) 0 (.base 15 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128803 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x128803) (movR64R64Effect 0x128803 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x128803 6 14).toInstrSpec (mov_r64_r64_effect_step 0x128803 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x128806 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x128806) (movR64R64Effect 0x128806 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x128806 2 13).toInstrSpec (mov_r64_r64_effect_step 0x128806 0x4c 0xea (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(13, 13), (14, 14), (15, 15)]) (p' := 0x1287ff) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(13, 13), (14, 14), (15, 15)]) (p' := 0x128803) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(13, 13), (14, 14), (15, 15)]) (p' := 0x128806) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(13, 13), (14, 14), (15, 15)]) (p' := 0x128809) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l1287fc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1287fc :=
  Rest.liftedBlock (rest_l1287fc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1287fc x hx)

theorem rest_l12880c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12880c bytes_l12880c) (entryMap (live .l12880c))
      2 0x12880c bytes_l12880c b_l12880c := by
  have f0 : InstrSpec 0x12880c [0x84, 0xC0] (fun s => s.RIP = 0x12880c) (testR8R8Effect 0x12880c 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x12880c 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x12880c 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12880e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12880e 5 0x8d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12880c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12880c :=
  Rest.liftedBlock (rest_l12880c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12880c x hx)

theorem rest_l128810 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128810 bytes_l128810) (entryMap (live .l128810))
      4 0x128810 bytes_l128810 b_l128810 := by
  have f0 : InstrSpec 0x128810 [0x49, 0x8B, 0x3F] (LoadPre 0x128810 (fun s => AddrMode.addr (.base 15 .none) s (0x128810 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128810 7 (.base 15 .none))
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x128810 7 (.base 15 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128810 0x49 (by decide) 7 (.base 15 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128813 [0x49, 0x8B, 0x47, 0x08] (LoadPre 0x128813 (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x128813 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128813 0 (.base 15 (.d8 0x8)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128813 0 (.base 15 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x128813 0x49 (by decide) 0 (.base 15 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128817 [0x48, 0x8D, 0x35, 0x0B, 0xB4, 0x0D, 0x00] (fun s => s.RIP = 0x128817) (leaR64Effect 0x128817 6 (.rip 0xdb40b))
      [] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x128817 6 (.rip 0xdb40b)).toInstrSpec (lea_r64_effect_step 0x128817 0x48 (by decide) 6 (.rip 0xdb40b) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12881e [0xBA, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12881e) (movR32Imm32Effect 0x12881e 5 2 0x2)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x12881e 5 2 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x12881e 0xba (by decide) 0x2) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(15, 15)]) (p' := 0x128813) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(15, 15)]) (p' := 0x128817) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(15, 15)]) (p' := 0x12881e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(15, 15)]) (p' := 0x128823) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128810 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128810 :=
  Rest.liftedBlock (rest_l128810 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128810 x hx)

theorem rest_l128826 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128826 bytes_l128826) (entryMap (live .l128826))
      2 0x128826 bytes_l128826 b_l128826 := by
  have f0 : InstrSpec 0x128826 [0x84, 0xC0] (fun s => s.RIP = 0x128826) (testR8R8Effect 0x128826 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128826 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x128826 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128828) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x128828 5 0xffffff6f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128826 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128826 :=
  Rest.liftedBlock (rest_l128826 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128826 x hx)

theorem rest_l12882e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12882e bytes_l12882e) (entryMap (live .l12882e))
      3 0x12882e bytes_l12882e b_l12882e := by
  have f0 : InstrSpec 0x12882e [0x48, 0x8B, 0x7D, 0xC0] (LoadPre 0x12882e (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x12882e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12882e 7 (.base 5 (.d8 0xc0)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12882e 7 (.base 5 (.d8 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x12882e 0x48 (by decide) 7 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128832 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x128832) (movR64R64Effect 0x128832 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x128832 6 15).toInstrSpec (mov_r64_r64_effect_step 0x128832 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128835 [0x48, 0x8B, 0x45, 0xC8] (LoadPre 0x128835 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x128835 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128835 0 (.base 5 (.d8 0xc8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128835 0 (.base 5 (.d8 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x128835 0x48 (by decide) 0 (.base 5 (.d8 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(5, 5), (15, 15)]) (p' := 0x128832) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(5, 5), (15, 15)]) (p' := 0x128835) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(5, 5), (15, 15)]) (p' := 0x128839) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l12882e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12882e :=
  Rest.liftedBlock (rest_l12882e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12882e x hx)

theorem rest_l12883c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12883c bytes_l12883c) (entryMap (live .l12883c))
      1 0x12883c bytes_l12883c b_l12883c := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x12883c 0xc4 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12883c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12883c :=
  Rest.liftedBlock (rest_l12883c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12883c x hx)

theorem rest_l128841 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128841 bytes_l128841) (entryMap (live .l128841))
      2 0x128841 bytes_l128841 b_l128841 := by
  have f0 : InstrSpec 0x128841 [0x84, 0xC0] (fun s => s.RIP = 0x128841) (testR8R8Effect 0x128841 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128841 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x128841 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128843) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128843 5 0x30) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128841 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128841 :=
  Rest.liftedBlock (rest_l128841 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128841 x hx)

theorem rest_l128845 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128845 bytes_l128845) (entryMap (live .l128845))
      7 0x128845 bytes_l128845 b_l128845 := by
  have f0 : InstrSpec 0x128845 [0x49, 0x8B, 0x3F] (LoadPre 0x128845 (fun s => AddrMode.addr (.base 15 .none) s (0x128845 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128845 7 (.base 15 .none))
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x128845 7 (.base 15 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128845 0x49 (by decide) 7 (.base 15 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128848 [0x49, 0x8B, 0x4F, 0x08] (LoadPre 0x128848 (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x128848 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128848 1 (.base 15 (.d8 0x8)))
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x128848 1 (.base 15 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x128848 0x49 (by decide) 1 (.base 15 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12884c [0x48, 0x8D, 0x05, 0xD8, 0xB3, 0x0D, 0x00] (fun s => s.RIP = 0x12884c) (leaR64Effect 0x12884c 0 (.rip 0xdb3d8))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x12884c 0 (.rip 0xdb3d8)).toInstrSpec (lea_r64_effect_step 0x12884c 0x48 (by decide) 0 (.rip 0xdb3d8) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x128853 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x128853) (movR64R64Effect 0x128853 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x128853 14 2).toInstrSpec (mov_r64_r64_effect_step 0x128853 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x128856 [0xBA, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128856) (movR32Imm32Effect 0x128856 5 2 0x3)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x128856 5 2 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x128856 0xba (by decide) 0x3) pre_rip
  have f5 : InstrSpec 0x12885b [0x49, 0x89, 0xF4] (fun s => s.RIP = 0x12885b) (movR64R64Effect 0x12885b 12 6)
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x12885b 12 6).toInstrSpec (mov_r64_r64_effect_step 0x12885b 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12885e [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x12885e) (movR64R64Effect 0x12885e 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12885e 6 0).toInstrSpec (mov_r64_r64_effect_step 0x12885e 0x48 0xc6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (6, 6), (15, 15)]) (p' := 0x128848) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (6, 6), (15, 15)]) (p' := 0x12884c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (6, 6), (15, 15)]) (p' := 0x128853) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (2, 2), (6, 6), (15, 15)]) (p' := 0x128856) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (6, 6), (15, 15)]) (p' := 0x12885b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 55), (6, 6), (15, 15)]) (p' := 0x12885e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 55), (15, 15)]) (p' := 0x128861) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128845 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128845 :=
  Rest.liftedBlock (rest_l128845 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128845 x hx)

theorem rest_l128864 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128864 bytes_l128864) (entryMap (live .l128864))
      5 0x128864 bytes_l128864 b_l128864 := by
  have f0 : InstrSpec 0x128864 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x128864) (movR64R64Effect 0x128864 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x128864 6 12).toInstrSpec (mov_r64_r64_effect_step 0x128864 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128867 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x128867) (movR64R64Effect 0x128867 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x128867 2 14).toInstrSpec (mov_r64_r64_effect_step 0x128867 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12886a [0x41, 0xB4, 0x01] (fun s => s.RIP = 0x12886a) (movR8Imm8Effect 0x12886a 3 12 0x1)
      [.gpr 12] [] [.reg 12, .rip] :=
    (movR8Imm8Effect_footprint 0x12886a 3 12 0x1).toInstrSpec (mov_r8_imm8_rex_effect_step 0x12886a 0x41 (by decide) 0xb4 (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x12886d [0x84, 0xC0] (fun s => s.RIP = 0x12886d) (testR8R8Effect 0x12886d 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x12886d 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x12886d 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128867) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12886a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12886d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12886f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel32_effect_step 0x12886f 5 0xffffff28) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128864 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128864 :=
  Rest.liftedBlock (rest_l128864 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128864 x hx)

theorem rest_l128875 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128875 bytes_l128875) (entryMap (live .l128875))
      14 0x128875 bytes_l128875 b_l128875 := by
  have f0 : InstrSpec 0x128875 [0xC6, 0x45, 0xD7, 0x01] (StorePre 0x128875 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd7)) s (0x128875 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x128875 (.base 5 (.d8 0xd7)) 0x1)
      [.gpr 5] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x128875 (.base 5 (.d8 0xd7)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x128875 (.base 5 (.d8 0xd7)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x128879 [0x49, 0x8B, 0x07] (LoadPre 0x128879 (fun s => AddrMode.addr (.base 15 .none) s (0x128879 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128879 0 (.base 15 .none))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128879 0 (.base 15 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128879 0x49 (by decide) 0 (.base 15 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12887c [0x49, 0x8B, 0x4F, 0x08] (LoadPre 0x12887c (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x12887c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12887c 1 (.base 15 (.d8 0x8)))
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12887c 1 (.base 15 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12887c 0x49 (by decide) 1 (.base 15 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x128880 [0x48, 0x89, 0x45, 0x90] (StorePre 0x128880 4 (fun s => AddrMode.addr (.base 5 (.d8 0x90)) s (0x128880 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128880 0 (.base 5 (.d8 0x90)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x128880 0 (.base 5 (.d8 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x128880 0x48 (by decide) 0 (.base 5 (.d8 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x128884 [0x48, 0x89, 0x4D, 0x98] (StorePre 0x128884 4 (fun s => AddrMode.addr (.base 5 (.d8 0x98)) s (0x128884 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128884 1 (.base 5 (.d8 0x98)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x128884 1 (.base 5 (.d8 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x128884 0x48 (by decide) 1 (.base 5 (.d8 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x128888 [0x48, 0x8D, 0x45, 0xD7] (fun s => s.RIP = 0x128888) (leaR64Effect 0x128888 0 (.base 5 (.d8 0xd7)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x128888 0 (.base 5 (.d8 0xd7))).toInstrSpec (lea_r64_effect_step 0x128888 0x48 (by decide) 0 (.base 5 (.d8 0xd7)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12888c [0x48, 0x89, 0x45, 0xA0] (StorePre 0x12888c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa0)) s (0x12888c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12888c 0 (.base 5 (.d8 0xa0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12888c 0 (.base 5 (.d8 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x12888c 0x48 (by decide) 0 (.base 5 (.d8 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x128890 [0x49, 0x8B, 0x47, 0x10] (LoadPre 0x128890 (fun s => AddrMode.addr (.base 15 (.d8 0x10)) s (0x128890 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128890 0 (.base 15 (.d8 0x10)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128890 0 (.base 15 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x128890 0x49 (by decide) 0 (.base 15 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x128894 [0x48, 0x89, 0x45, 0xB8] (StorePre 0x128894 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x128894 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128894 0 (.base 5 (.d8 0xb8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x128894 0 (.base 5 (.d8 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x128894 0x48 (by decide) 0 (.base 5 (.d8 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x128898 [0x48, 0x8D, 0x7D, 0x90] (fun s => s.RIP = 0x128898) (leaR64Effect 0x128898 7 (.base 5 (.d8 0x90)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x128898 7 (.base 5 (.d8 0x90))).toInstrSpec (lea_r64_effect_step 0x128898 0x48 (by decide) 7 (.base 5 (.d8 0x90)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x12889c [0x48, 0x89, 0x7D, 0xA8] (StorePre 0x12889c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x12889c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12889c 7 (.base 5 (.d8 0xa8)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12889c 7 (.base 5 (.d8 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x12889c 0x48 (by decide) 7 (.base 5 (.d8 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1288a0 [0x48, 0x8D, 0x05, 0xE1, 0xB4, 0x0D, 0x00] (fun s => s.RIP = 0x1288a0) (leaR64Effect 0x1288a0 0 (.rip 0xdb4e1))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1288a0 0 (.rip 0xdb4e1)).toInstrSpec (lea_r64_effect_step 0x1288a0 0x48 (by decide) 0 (.rip 0xdb4e1) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1288a7 [0x48, 0x89, 0x45, 0xB0] (StorePre 0x1288a7 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb0)) s (0x1288a7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1288a7 0 (.base 5 (.d8 0xb0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1288a7 0 (.base 5 (.d8 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x1288a7 0x48 (by decide) 0 (.base 5 (.d8 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1288ab [0xFF, 0x15, 0x67, 0xB5, 0x0D, 0x00] (GoesTo (CallMemPre 0x1288ab (.rip 0xdb567)) (callEffect (callMemPtr 0x1288ab (.rip 0xdb567)) (0x1288ab + BitVec.ofNat 64 (callMemLen (.rip 0xdb567)))) 0x129dd0) (callEffect (callMemPtr 0x1288ab (.rip 0xdb567)) (0x1288ab + BitVec.ofNat 64 (callMemLen (.rip 0xdb567))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1288ab (.rip 0xdb567)).toInstrSpec (call_m64_effect_step 0x1288ab (.rip 0xdb567) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129dd0
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128879) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12887c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128880) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 54), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128884) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 54), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128888) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12888c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 60), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128890) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128894) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128898) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 63), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12889c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 63), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1288a0) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1288a7) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1288ab) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 69), (1, 56), (2, 2), (3, 3), (4, 72), (5, 5), (6, 6), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129dd0) f13 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 74) (by decide) (by decide) rfl rfl

theorem block_l128875 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128875 :=
  Rest.liftedBlock (rest_l128875 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128875 x hx)

theorem rest_l1288b1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1288b1 bytes_l1288b1) (entryMap (live .l1288b1))
      2 0x1288b1 bytes_l1288b1 b_l1288b1 := by
  have f0 : InstrSpec 0x1288b1 [0x84, 0xC0] (fun s => s.RIP = 0x1288b1) (testR8R8Effect 0x1288b1 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1288b1 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x1288b1 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1288b3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1288b3 5 0xfffffee4) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1288b1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1288b1 :=
  Rest.liftedBlock (rest_l1288b1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1288b1 x hx)

theorem rest_l1288b9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1288b9 bytes_l1288b9) (entryMap (live .l1288b9))
      4 0x1288b9 bytes_l1288b9 b_l1288b9 := by
  have f0 : InstrSpec 0x1288b9 [0x48, 0x8D, 0x35, 0x69, 0xB3, 0x0D, 0x00] (fun s => s.RIP = 0x1288b9) (leaR64Effect 0x1288b9 6 (.rip 0xdb369))
      [] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1288b9 6 (.rip 0xdb369)).toInstrSpec (lea_r64_effect_step 0x1288b9 0x48 (by decide) 6 (.rip 0xdb369) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1288c0 [0x48, 0x8D, 0x7D, 0x90] (fun s => s.RIP = 0x1288c0) (leaR64Effect 0x1288c0 7 (.base 5 (.d8 0x90)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1288c0 7 (.base 5 (.d8 0x90))).toInstrSpec (lea_r64_effect_step 0x1288c0 0x48 (by decide) 7 (.base 5 (.d8 0x90)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1288c4 [0xBA, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1288c4) (movR32Imm32Effect 0x1288c4 5 2 0x2)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1288c4 5 2 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x1288c4 0xba (by decide) 0x2) pre_rip
  have f3 : InstrSpec 0x1288c9 [0xFF, 0x15, 0x49, 0xB5, 0x0D, 0x00] (GoesTo (CallMemPre 0x1288c9 (.rip 0xdb549)) (callEffect (callMemPtr 0x1288c9 (.rip 0xdb549)) (0x1288c9 + BitVec.ofNat 64 (callMemLen (.rip 0xdb549)))) 0x129dd0) (callEffect (callMemPtr 0x1288c9 (.rip 0xdb549)) (0x1288c9 + BitVec.ofNat 64 (callMemLen (.rip 0xdb549))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1288c9 (.rip 0xdb549)).toInstrSpec (call_m64_effect_step 0x1288c9 (.rip 0xdb549) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129dd0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1288c0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1288c4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1288c9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129dd0) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1288b9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1288b9 :=
  Rest.liftedBlock (rest_l1288b9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1288b9 x hx)

theorem rest_l1288cf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1288cf bytes_l1288cf) (entryMap (live .l1288cf))
      2 0x1288cf bytes_l1288cf b_l1288cf := by
  have f0 : InstrSpec 0x1288cf [0x84, 0xC0] (fun s => s.RIP = 0x1288cf) (testR8R8Effect 0x1288cf 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1288cf 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x1288cf 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1288d1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1288d1 5 0xfffffec6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1288cf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1288cf :=
  Rest.liftedBlock (rest_l1288cf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1288cf x hx)

theorem rest_l1288d7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1288d7 bytes_l1288d7) (entryMap (live .l1288d7))
      3 0x1288d7 bytes_l1288d7 b_l1288d7 := by
  have f0 : InstrSpec 0x1288d7 [0x48, 0x8D, 0x75, 0xA8] (fun s => s.RIP = 0x1288d7) (leaR64Effect 0x1288d7 6 (.base 5 (.d8 0xa8)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1288d7 6 (.base 5 (.d8 0xa8))).toInstrSpec (lea_r64_effect_step 0x1288d7 0x48 (by decide) 6 (.base 5 (.d8 0xa8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1288db [0x48, 0x8B, 0x7D, 0xC0] (LoadPre 0x1288db (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x1288db + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1288db 7 (.base 5 (.d8 0xc0)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1288db 7 (.base 5 (.d8 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x1288db 0x48 (by decide) 7 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1288df [0x48, 0x8B, 0x45, 0xC8] (LoadPre 0x1288df (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x1288df + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1288df 0 (.base 5 (.d8 0xc8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1288df 0 (.base 5 (.d8 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x1288df 0x48 (by decide) 0 (.base 5 (.d8 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(5, 5)]) (p' := 0x1288db) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(5, 5)]) (p' := 0x1288df) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(5, 5)]) (p' := 0x1288e3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l1288d7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1288d7 :=
  Rest.liftedBlock (rest_l1288d7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1288d7 x hx)

theorem rest_l1288e6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1288e6 bytes_l1288e6) (entryMap (live .l1288e6))
      2 0x1288e6 bytes_l1288e6 b_l1288e6 := by
  have f0 : InstrSpec 0x1288e6 [0x84, 0xC0] (fun s => s.RIP = 0x1288e6) (testR8R8Effect 0x1288e6 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1288e6 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x1288e6 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1288e8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1288e8 5 0xfffffeaf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1288e6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1288e6 :=
  Rest.liftedBlock (rest_l1288e6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1288e6 x hx)

theorem rest_l1288ee [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1288ee bytes_l1288ee) (entryMap (live .l1288ee))
      4 0x1288ee bytes_l1288ee b_l1288ee := by
  have f0 : InstrSpec 0x1288ee [0x48, 0x8B, 0x7D, 0xA8] (LoadPre 0x1288ee (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x1288ee + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1288ee 7 (.base 5 (.d8 0xa8)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1288ee 7 (.base 5 (.d8 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x1288ee 0x48 (by decide) 7 (.base 5 (.d8 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1288f2 [0x48, 0x8B, 0x45, 0xB0] (LoadPre 0x1288f2 (fun s => AddrMode.addr (.base 5 (.d8 0xb0)) s (0x1288f2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1288f2 0 (.base 5 (.d8 0xb0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1288f2 0 (.base 5 (.d8 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x1288f2 0x48 (by decide) 0 (.base 5 (.d8 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1288f6 [0x48, 0x8D, 0x35, 0x31, 0xB3, 0x0D, 0x00] (fun s => s.RIP = 0x1288f6) (leaR64Effect 0x1288f6 6 (.rip 0xdb331))
      [] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1288f6 6 (.rip 0xdb331)).toInstrSpec (lea_r64_effect_step 0x1288f6 0x48 (by decide) 6 (.rip 0xdb331) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1288fd [0xBA, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1288fd) (movR32Imm32Effect 0x1288fd 5 2 0x2)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1288fd 5 2 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x1288fd 0xba (by decide) 0x2) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(5, 5)]) (p' := 0x1288f2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(5, 5)]) (p' := 0x1288f6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(5, 5)]) (p' := 0x1288fd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(5, 5)]) (p' := 0x128902) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l1288ee [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1288ee :=
  Rest.liftedBlock (rest_l1288ee code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1288ee x hx)

theorem rest_l128905 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128905 bytes_l128905) (entryMap (live .l128905))
      2 0x128905 bytes_l128905 b_l128905 := by
  have f0 : InstrSpec 0x128905 [0x41, 0x89, 0xC4] (fun s => s.RIP = 0x128905) (movR32R32Effect 0x128905 3 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x128905 3 12 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x128905 0x41 0xc4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128908) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x128908 0xfffffe90 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l128905 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128905 :=
  Rest.liftedBlock (rest_l128905 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128905 x hx)

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

theorem_by block_l12873d_eval :
    program.runBlock (dialect code) ⟨.l12873d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128772_eval :
    program.runBlock (dialect code) ⟨.l128772, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12879d_eval :
    program.runBlock (dialect code) ⟨.l12879d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1287b7_eval :
    program.runBlock (dialect code) ⟨.l1287b7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1287cd_eval :
    program.runBlock (dialect code) ⟨.l1287cd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1287f8_eval :
    program.runBlock (dialect code) ⟨.l1287f8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1287fc_eval :
    program.runBlock (dialect code) ⟨.l1287fc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12880c_eval :
    program.runBlock (dialect code) ⟨.l12880c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128810_eval :
    program.runBlock (dialect code) ⟨.l128810, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128826_eval :
    program.runBlock (dialect code) ⟨.l128826, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12882e_eval :
    program.runBlock (dialect code) ⟨.l12882e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12883c_eval :
    program.runBlock (dialect code) ⟨.l12883c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128841_eval :
    program.runBlock (dialect code) ⟨.l128841, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128845_eval :
    program.runBlock (dialect code) ⟨.l128845, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128864_eval :
    program.runBlock (dialect code) ⟨.l128864, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128875_eval :
    program.runBlock (dialect code) ⟨.l128875, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1288b1_eval :
    program.runBlock (dialect code) ⟨.l1288b1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1288b9_eval :
    program.runBlock (dialect code) ⟨.l1288b9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1288cf_eval :
    program.runBlock (dialect code) ⟨.l1288cf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1288d7_eval :
    program.runBlock (dialect code) ⟨.l1288d7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1288e6_eval :
    program.runBlock (dialect code) ⟨.l1288e6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1288ee_eval :
    program.runBlock (dialect code) ⟨.l1288ee, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128905_eval :
    program.runBlock (dialect code) ⟨.l128905, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
