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

theorem rest_l124670 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124670 bytes_l124670) (entryMap (live .l124670))
      13 0x124670 bytes_l124670 b_l124670 := by
  have f0 : InstrSpec 0x124670 [0x55] (PushPre 0x124670 1) (pushR64Effect 0x124670 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124670 1 5).toInstrSpec (push_r64_effect_step 0x124670 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x124671 [0x41, 0x57] (PushPre 0x124671 2) (pushR64Effect 0x124671 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124671 2 15).toInstrSpec (push_r64_rex_effect_step 0x124671 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x124673 [0x41, 0x56] (PushPre 0x124673 2) (pushR64Effect 0x124673 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124673 2 14).toInstrSpec (push_r64_rex_effect_step 0x124673 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x124675 [0x41, 0x55] (PushPre 0x124675 2) (pushR64Effect 0x124675 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124675 2 13).toInstrSpec (push_r64_rex_effect_step 0x124675 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x124677 [0x41, 0x54] (PushPre 0x124677 2) (pushR64Effect 0x124677 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124677 2 12).toInstrSpec (push_r64_rex_effect_step 0x124677 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x124679 [0x53] (PushPre 0x124679 1) (pushR64Effect 0x124679 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124679 1 3).toInstrSpec (push_r64_effect_step 0x124679 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x12467a [0x48, 0x83, 0xEC, 0x38] (fun s => s.RIP = 0x12467a) (subR64Imm8Effect 0x12467a 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x12467a 4 0x38).toInstrSpec (sub_r64_imm8_effect_step 0x12467a 0x48 0xec 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12467e [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x12467e) (movR64R64Effect 0x12467e 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x12467e 3 7).toInstrSpec (mov_r64_r64_effect_step 0x12467e 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x124681 [0x89, 0xF5] (fun s => s.RIP = 0x124681) (movR32R32Effect 0x124681 2 5 6)
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x124681 2 5 6).toInstrSpec (mov_r32_r32_effect_step 0x124681 0xf5 (by decide)) pre_rip
  have f9 : InstrSpec 0x124683 [0x40, 0x80, 0xE5, 0x20] (fun s => s.RIP = 0x124683) (andR8Imm8Effect 0x124683 4 5 0x20)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x124683 4 5 0x20).toInstrSpec (and_r8_imm8_rex_effect_step 0x124683 0x40 0xe5 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x124687 [0x40, 0x80, 0xE6, 0x1F] (fun s => s.RIP = 0x124687) (andR8Imm8Effect 0x124687 4 6 0x1f)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x124687 4 6 0x1f).toInstrSpec (and_r8_imm8_rex_effect_step 0x124687 0x40 0xe6 0x1f (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12468b [0x40, 0x80, 0xFE, 0x1F] (fun s => s.RIP = 0x12468b) (cmpR8Imm8Effect 0x12468b 4 6 0x1f)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x12468b 4 6 0x1f).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x12468b 0x40 0xfe 0x1f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124671) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124673) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124675) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124677) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124679) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12467a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12467e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124681) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124683) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124687) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 71), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12468b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 71), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12468f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 77) (jcc_rel8_effect_step 0x12468f 5 0x5a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124670 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124670 :=
  Rest.liftedBlock (rest_l124670 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124670 x hx)

theorem rest_l124691 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124691 bytes_l124691) (entryMap (live .l124691))
      5 0x124691 bytes_l124691 b_l124691 := by
  have f0 : InstrSpec 0x124691 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x124691) (movR64R64Effect 0x124691 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x124691 14 2).toInstrSpec (mov_r64_r64_effect_step 0x124691 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124694 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x124694) (movR64R64Effect 0x124694 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x124694 7 4).toInstrSpec (mov_r64_r64_effect_step 0x124694 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124697 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x124697) (movR64R64Effect 0x124697 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x124697 6 2).toInstrSpec (mov_r64_r64_effect_step 0x124697 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12469a [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12469a) (movR32Imm32Effect 0x12469a 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x12469a 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x12469a 0xba (by decide) 0x1) pre_rip
  have f4 : InstrSpec 0x12469f [0xE8, 0xDC, 0x34, 0x00, 0x00] (PushPre 0x12469f 5) (callEffect (fun _ => 0x127b80) 0x1246a4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12469f 0x127b80 0x1246a4).toInstrSpec (call_rel32_effect_step 0x12469f 0x34dc (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124694) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124697) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12469a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12469f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l124691 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124691 :=
  Rest.liftedBlock (rest_l124691 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124691 x hx)

theorem rest_l1246a4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1246a4 bytes_l1246a4) (entryMap (live .l1246a4))
      3 0x1246a4 bytes_l1246a4 b_l1246a4 := by
  have f0 : InstrSpec 0x1246a4 [0x8B, 0x04, 0x24] (LoadPre 0x1246a4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1246a4 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1246a4 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1246a4 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x1246a4 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1246a7 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x1246a7) (cmpR32Imm8Effect 0x1246a7 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1246a7 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1246a7 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1246a7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1246aa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1246aa 5 0x1a5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1246a4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1246a4 :=
  Rest.liftedBlock (rest_l1246a4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1246a4 x hx)

theorem rest_l1246b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1246b0 bytes_l1246b0) (entryMap (live .l1246b0))
      3 0x1246b0 bytes_l1246b0 b_l1246b0 := by
  have f0 : InstrSpec 0x1246b0 [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x1246b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1246b0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1246b0 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1246b0 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1246b0 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1246b5 [0x48, 0x83, 0xFE, 0x01] (fun s => s.RIP = 0x1246b5) (cmpR64Imm8Effect 0x1246b5 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1246b5 6 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x1246b5 0x48 0xfe 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1246b5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1246b9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1246b9 5 0x1e4) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1246b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1246b0 :=
  Rest.liftedBlock (rest_l1246b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1246b0 x hx)

theorem rest_l1246bf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1246bf bytes_l1246bf) (entryMap (live .l1246bf))
      6 0x1246bf bytes_l1246bf b_l1246bf := by
  have f0 : InstrSpec 0x1246bf [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x1246bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1246bf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1246bf 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1246bf 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1246bf 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1246c4 [0x44, 0x0F, 0xB6, 0x38] (LoadPre 0x1246c4 (fun s => AddrMode.addr (.base 0 .none) s (0x1246c4 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1246c4 4 15 (.base 0 .none))
      [.gpr 0] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x1246c4 4 15 (.base 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1246c4 0x44 (by decide) 7 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1246c8 [0x44, 0x89, 0xF8] (fun s => s.RIP = 0x1246c8) (movR32R32Effect 0x1246c8 3 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1246c8 3 0 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x1246c8 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1246cb [0x41, 0x83, 0xE7, 0x7F] (fun s => s.RIP = 0x1246cb) (andR32Imm8Effect 0x1246cb 4 15 0x7f)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1246cb 4 15 0x7f).toInstrSpec (and_r32_imm8_rex_effect_step 0x1246cb 0x41 0xe7 0x7f (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1246cf [0x84, 0xC0] (fun s => s.RIP = 0x1246cf) (testR8R8Effect 0x1246cf 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1246cf 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x1246cf 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1246c4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1246c8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1246cb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1246cf) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 59), (20, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1246d1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x1246d1 8 0x32) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1246bf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1246bf :=
  Rest.liftedBlock (rest_l1246bf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1246bf x hx)

theorem rest_l1246d3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1246d3 bytes_l1246d3) (entryMap (live .l1246d3))
      2 0x1246d3 bytes_l1246d3 b_l1246d3 := by
  have f0 : InstrSpec 0x1246d3 [0x41, 0x80, 0xFF, 0x1F] (fun s => s.RIP = 0x1246d3) (cmpR8Imm8Effect 0x1246d3 4 15 0x1f)
      [.gpr 15] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x1246d3 4 15 0x1f).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x1246d3 0x41 0xff 0x1f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1246d7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1246d7 2 0x11c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1246d3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1246d3 :=
  Rest.liftedBlock (rest_l1246d3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1246d3 x hx)

theorem rest_l1246dd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1246dd bytes_l1246dd) (entryMap (live .l1246dd))
      4 0x1246dd bytes_l1246dd b_l1246dd := by
  have f0 : InstrSpec 0x1246dd [0x40, 0xC0, 0xED, 0x05] (fun s => s.RIP = 0x1246dd) (shrR8Effect 0x1246dd 4 5 5)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR8Effect_footprint 0x1246dd 4 5 5).toInstrSpec (shr_r8_imm8_rex_effect_step 0x1246dd 0x40 0xed 0x5 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1246e1 [0x40, 0x88, 0x6B, 0x04] (StorePre 0x1246e1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1246e1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1246e1 4 5 (.base 3 (.d8 0x4)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x1246e1 4 5 (.base 3 (.d8 0x4))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1246e1 0x40 (by decide) 5 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1246e5 [0x44, 0x89, 0x7B, 0x08] (StorePre 0x1246e5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1246e5 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1246e5 15 (.base 3 (.d8 0x8)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x1246e5 15 (.base 3 (.d8 0x8))).toInstrSpec (mov_m32_r32_effect_step 0x1246e5 0x44 (by decide) 7 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1246e1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1246e5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1246e9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x1246e9 0xf (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1246dd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1246dd :=
  Rest.liftedBlock (rest_l1246dd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1246dd x hx)

theorem rest_l1246eb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1246eb bytes_l1246eb) (entryMap (live .l1246eb))
      4 0x1246eb bytes_l1246eb b_l1246eb := by
  have f0 : InstrSpec 0x1246eb [0x40, 0x0F, 0xB6, 0xC6] (fun s => s.RIP = 0x1246eb) (movzxR32R8Effect 0x1246eb 4 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x1246eb 4 0 6).toInstrSpec (movzx_r32_r8_rex_effect_step 0x1246eb 0x40 (by decide) 0xc6 (by decide)) pre_rip
  have f1 : InstrSpec 0x1246ef [0x40, 0xC0, 0xED, 0x05] (fun s => s.RIP = 0x1246ef) (shrR8Effect 0x1246ef 4 5 5)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR8Effect_footprint 0x1246ef 4 5 5).toInstrSpec (shr_r8_imm8_rex_effect_step 0x1246ef 0x40 0xed 0x5 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1246f3 [0x40, 0x88, 0x6B, 0x04] (StorePre 0x1246f3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1246f3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1246f3 4 5 (.base 3 (.d8 0x4)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x1246f3 4 5 (.base 3 (.d8 0x4))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1246f3 0x40 (by decide) 5 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1246f7 [0x89, 0x43, 0x08] (StorePre 0x1246f7 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1246f7 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1246f7 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1246f7 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x1246f7 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1246ef) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1246f3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1246f7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1246fa) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l1246eb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1246eb :=
  Rest.liftedBlock (rest_l1246eb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1246eb x hx)

theorem rest_l1246fa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1246fa bytes_l1246fa) (entryMap (live .l1246fa))
      2 0x1246fa bytes_l1246fa b_l1246fa := by
  have f0 : InstrSpec 0x1246fa [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x1246fa 6 (fun s => AddrMode.addr (.base 3 .none) s (0x1246fa + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x1246fa 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1246fa 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x1246fa (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124700) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 54) (jmp_rel32_effect_step 0x124700 0x18f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1246fa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1246fa :=
  Rest.liftedBlock (rest_l1246fa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1246fa x hx)

theorem rest_l124705 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124705 bytes_l124705) (entryMap (live .l124705))
      2 0x124705 bytes_l124705 b_l124705 := by
  have f0 : InstrSpec 0x124705 [0x45, 0x84, 0xFF] (fun s => s.RIP = 0x124705) (testR8R8Effect 0x124705 3 15 15)
      [.gpr 15, .gpr 15] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x124705 3 15 15).toInstrSpec (test_r8_r8_rex_effect_step 0x124705 0x45 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124708) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x124708 4 0xeb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124705 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124705 :=
  Rest.liftedBlock (rest_l124705 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124705 x hx)

theorem rest_l12470e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12470e bytes_l12470e) (entryMap (live .l12470e))
      4 0x12470e bytes_l12470e b_l12470e := by
  have f0 : InstrSpec 0x12470e [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x12470e) (movR64R64Effect 0x12470e 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12470e 7 4).toInstrSpec (mov_r64_r64_effect_step 0x12470e 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124711 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x124711) (movR64R64Effect 0x124711 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x124711 6 14).toInstrSpec (mov_r64_r64_effect_step 0x124711 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124714 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x124714) (movR32Imm32Effect 0x124714 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x124714 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x124714 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x124719 [0xE8, 0x62, 0x34, 0x00, 0x00] (PushPre 0x124719 5) (callEffect (fun _ => 0x127b80) 0x12471e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124719 0x127b80 0x12471e).toInstrSpec (call_rel32_effect_step 0x124719 0x3462 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124711) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124714) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124719) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l12470e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12470e :=
  Rest.liftedBlock (rest_l12470e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12470e x hx)

theorem rest_l12471e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12471e bytes_l12471e) (entryMap (live .l12471e))
      3 0x12471e bytes_l12471e b_l12471e := by
  have f0 : InstrSpec 0x12471e [0x8B, 0x04, 0x24] (LoadPre 0x12471e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12471e + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x12471e 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x12471e 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x12471e 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124721 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x124721) (cmpR32Imm8Effect 0x124721 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124721 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124721 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124721) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124724) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x124724 5 0x12b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12471e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12471e :=
  Rest.liftedBlock (rest_l12471e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12471e x hx)

theorem rest_l12472a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12472a bytes_l12472a) (entryMap (live .l12472a))
      3 0x12472a bytes_l12472a b_l12472a := by
  have f0 : InstrSpec 0x12472a [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x12472a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12472a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12472a 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12472a 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x12472a 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12472f [0x48, 0x83, 0xFE, 0x01] (fun s => s.RIP = 0x12472f) (cmpR64Imm8Effect 0x12472f 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x12472f 6 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x12472f 0x48 0xfe 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12472f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124733) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x124733 5 0x16a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12472a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12472a :=
  Rest.liftedBlock (rest_l12472a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12472a x hx)

theorem rest_l124739 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124739 bytes_l124739) (entryMap (live .l124739))
      9 0x124739 bytes_l124739 b_l124739 := by
  have f0 : InstrSpec 0x124739 [0x44, 0x89, 0xF8] (fun s => s.RIP = 0x124739) (movR32R32Effect 0x124739 3 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x124739 3 0 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x124739 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12473c [0xC1, 0xE0, 0x07] (fun s => s.RIP = 0x12473c) (shlR32Effect 0x12473c 3 0 7)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x12473c 3 0 7).toInstrSpec (shl_r32_imm8_effect_step 0x12473c 0xe0 0x7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12473f [0x48, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x12473f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12473f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12473f 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12473f 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12473f 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x124744 [0x44, 0x0F, 0xB6, 0x21] (LoadPre 0x124744 (fun s => AddrMode.addr (.base 1 .none) s (0x124744 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x124744 4 12 (.base 1 .none))
      [.gpr 1] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x124744 4 12 (.base 1 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x124744 0x44 (by decide) 4 (.base 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x124748 [0x44, 0x89, 0xE1] (fun s => s.RIP = 0x124748) (movR32R32Effect 0x124748 3 1 12)
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x124748 3 1 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x124748 0x44 0xe1 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12474b [0x41, 0x83, 0xE4, 0x7F] (fun s => s.RIP = 0x12474b) (andR32Imm8Effect 0x12474b 4 12 0x7f)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x12474b 4 12 0x7f).toInstrSpec (and_r32_imm8_rex_effect_step 0x12474b 0x41 0xe4 0x7f (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12474f [0x41, 0x09, 0xC4] (fun s => s.RIP = 0x12474f) (orR32R32Effect 0x12474f 3 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (orR32R32Effect_footprint 0x12474f 3 12 0).toInstrSpec (or_r32_r32_rex_effect_step 0x12474f 0x41 0xc4 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x124752 [0x84, 0xC9] (fun s => s.RIP = 0x124752) (testR8R8Effect 0x124752 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x124752 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x124752 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12473c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12473f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124744) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124748) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12474b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12474f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124752) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124754) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 69) (jcc_rel8_effect_step 0x124754 8 0x5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124739 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124739 :=
  Rest.liftedBlock (rest_l124739 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124739 x hx)

theorem rest_l124756 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124756 bytes_l124756) (entryMap (live .l124756))
      2 0x124756 bytes_l124756 b_l124756 := by
  have f0 : InstrSpec 0x124756 [0x45, 0x89, 0xE7] (fun s => s.RIP = 0x124756) (movR32R32Effect 0x124756 3 15 12)
      [.gpr 12] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x124756 3 15 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x124756 0x45 0xe7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124759) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x124759 0x82 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124756 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124756 :=
  Rest.liftedBlock (rest_l124756 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124756 x hx)

theorem rest_l12475b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12475b bytes_l12475b) (entryMap (live .l12475b))
      4 0x12475b bytes_l12475b b_l12475b := by
  have f0 : InstrSpec 0x12475b [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x12475b) (movR64R64Effect 0x12475b 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12475b 7 4).toInstrSpec (mov_r64_r64_effect_step 0x12475b 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12475e [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x12475e) (movR64R64Effect 0x12475e 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12475e 6 14).toInstrSpec (mov_r64_r64_effect_step 0x12475e 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124761 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x124761) (movR32Imm32Effect 0x124761 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x124761 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x124761 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x124766 [0xE8, 0x15, 0x34, 0x00, 0x00] (PushPre 0x124766 5) (callEffect (fun _ => 0x127b80) 0x12476b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124766 0x127b80 0x12476b).toInstrSpec (call_rel32_effect_step 0x124766 0x3415 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12475e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124761) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124766) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l12475b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12475b :=
  Rest.liftedBlock (rest_l12475b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12475b x hx)

theorem rest_l12476b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12476b bytes_l12476b) (entryMap (live .l12476b))
      3 0x12476b bytes_l12476b b_l12476b := by
  have f0 : InstrSpec 0x12476b [0x8B, 0x04, 0x24] (LoadPre 0x12476b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12476b + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x12476b 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x12476b 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x12476b 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12476e [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x12476e) (cmpR32Imm8Effect 0x12476e 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x12476e 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x12476e 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12476e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124771) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x124771 5 0xde) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12476b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12476b :=
  Rest.liftedBlock (rest_l12476b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12476b x hx)

theorem rest_l124777 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124777 bytes_l124777) (entryMap (live .l124777))
      3 0x124777 bytes_l124777 b_l124777 := by
  have f0 : InstrSpec 0x124777 [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x124777 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124777 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124777 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124777 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x124777 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12477c [0x48, 0x83, 0xFE, 0x01] (fun s => s.RIP = 0x12477c) (cmpR64Imm8Effect 0x12477c 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x12477c 6 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x12477c 0x48 0xfe 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12477c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124780) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x124780 5 0x11d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124777 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124777 :=
  Rest.liftedBlock (rest_l124777 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124777 x hx)

theorem rest_l124786 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124786 bytes_l124786) (entryMap (live .l124786))
      8 0x124786 bytes_l124786 b_l124786 := by
  have f0 : InstrSpec 0x124786 [0x41, 0xC1, 0xE4, 0x07] (fun s => s.RIP = 0x124786) (shlR32Effect 0x124786 4 12 7)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shlR32Effect_footprint 0x124786 4 12 7).toInstrSpec (shl_r32_imm8_rex_effect_step 0x124786 0x41 0xe4 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12478a [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x12478a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12478a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12478a 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12478a 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12478a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12478f [0x44, 0x0F, 0xB6, 0x28] (LoadPre 0x12478f (fun s => AddrMode.addr (.base 0 .none) s (0x12478f + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x12478f 4 13 (.base 0 .none))
      [.gpr 0] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x12478f 4 13 (.base 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x12478f 0x44 (by decide) 5 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x124793 [0x44, 0x89, 0xE8] (fun s => s.RIP = 0x124793) (movR32R32Effect 0x124793 3 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x124793 3 0 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x124793 0x44 0xe8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x124796 [0x41, 0x83, 0xE5, 0x7F] (fun s => s.RIP = 0x124796) (andR32Imm8Effect 0x124796 4 13 0x7f)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x124796 4 13 0x7f).toInstrSpec (and_r32_imm8_rex_effect_step 0x124796 0x41 0xe5 0x7f (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12479a [0x45, 0x09, 0xE5] (fun s => s.RIP = 0x12479a) (orR32R32Effect 0x12479a 3 13 12)
      [.gpr 13, .gpr 12] [] [.reg 13, .flags, .rip] :=
    (orR32R32Effect_footprint 0x12479a 3 13 12).toInstrSpec (or_r32_r32_rex_effect_step 0x12479a 0x45 0xe5 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12479d [0x84, 0xC0] (fun s => s.RIP = 0x12479d) (testR8R8Effect 0x12479d 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x12479d 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x12479d 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12478a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12478f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124793) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124796) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12479a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 63), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12479d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 63), (14, 14), (15, 15), (20, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12479f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 67) (jcc_rel8_effect_step 0x12479f 8 0x8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124786 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124786 :=
  Rest.liftedBlock (rest_l124786 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124786 x hx)

theorem rest_l1247a1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1247a1 bytes_l1247a1) (entryMap (live .l1247a1))
      2 0x1247a1 bytes_l1247a1 b_l1247a1 := by
  have f0 : InstrSpec 0x1247a1 [0x45, 0x89, 0xEF] (fun s => s.RIP = 0x1247a1) (movR32R32Effect 0x1247a1 3 15 13)
      [.gpr 13] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x1247a1 3 15 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x1247a1 0x45 0xef (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1247a4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x1247a4 0xffffff34 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1247a1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1247a1 :=
  Rest.liftedBlock (rest_l1247a1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1247a1 x hx)

theorem rest_l1247a9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1247a9 bytes_l1247a9) (entryMap (live .l1247a9))
      4 0x1247a9 bytes_l1247a9 b_l1247a9 := by
  have f0 : InstrSpec 0x1247a9 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x1247a9) (movR64R64Effect 0x1247a9 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1247a9 7 4).toInstrSpec (mov_r64_r64_effect_step 0x1247a9 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1247ac [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x1247ac) (movR64R64Effect 0x1247ac 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1247ac 6 14).toInstrSpec (mov_r64_r64_effect_step 0x1247ac 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1247af [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1247af) (movR32Imm32Effect 0x1247af 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1247af 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1247af 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x1247b4 [0xE8, 0xC7, 0x33, 0x00, 0x00] (PushPre 0x1247b4 5) (callEffect (fun _ => 0x127b80) 0x1247b9)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1247b4 0x127b80 0x1247b9).toInstrSpec (call_rel32_effect_step 0x1247b4 0x33c7 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1247ac) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1247af) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1247b4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1247a9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1247a9 :=
  Rest.liftedBlock (rest_l1247a9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1247a9 x hx)

theorem rest_l1247b9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1247b9 bytes_l1247b9) (entryMap (live .l1247b9))
      3 0x1247b9 bytes_l1247b9 b_l1247b9 := by
  have f0 : InstrSpec 0x1247b9 [0x8B, 0x04, 0x24] (LoadPre 0x1247b9 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1247b9 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1247b9 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1247b9 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x1247b9 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1247bc [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x1247bc) (cmpR32Imm8Effect 0x1247bc 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1247bc 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1247bc 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1247bc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1247bf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1247bf 5 0x90) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1247b9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1247b9 :=
  Rest.liftedBlock (rest_l1247b9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1247b9 x hx)

theorem rest_l1247c5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1247c5 bytes_l1247c5) (entryMap (live .l1247c5))
      3 0x1247c5 bytes_l1247c5 b_l1247c5 := by
  have f0 : InstrSpec 0x1247c5 [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x1247c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1247c5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1247c5 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1247c5 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1247c5 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1247ca [0x48, 0x83, 0xFE, 0x01] (fun s => s.RIP = 0x1247ca) (cmpR64Imm8Effect 0x1247ca 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1247ca 6 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x1247ca 0x48 0xfe 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1247ca) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1247ce) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1247ce 5 0xcf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1247c5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1247c5 :=
  Rest.liftedBlock (rest_l1247c5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1247c5 x hx)

theorem rest_l1247d4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1247d4 bytes_l1247d4) (entryMap (live .l1247d4))
      8 0x1247d4 bytes_l1247d4 b_l1247d4 := by
  have f0 : InstrSpec 0x1247d4 [0x41, 0xC1, 0xE5, 0x07] (fun s => s.RIP = 0x1247d4) (shlR32Effect 0x1247d4 4 13 7)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shlR32Effect_footprint 0x1247d4 4 13 7).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1247d4 0x41 0xe5 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1247d8 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x1247d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1247d8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1247d8 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1247d8 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1247d8 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1247dd [0x44, 0x0F, 0xB6, 0x20] (LoadPre 0x1247dd (fun s => AddrMode.addr (.base 0 .none) s (0x1247dd + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1247dd 4 12 (.base 0 .none))
      [.gpr 0] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x1247dd 4 12 (.base 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1247dd 0x44 (by decide) 4 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1247e1 [0x44, 0x89, 0xE0] (fun s => s.RIP = 0x1247e1) (movR32R32Effect 0x1247e1 3 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1247e1 3 0 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x1247e1 0x44 0xe0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1247e4 [0x41, 0x83, 0xE4, 0x7F] (fun s => s.RIP = 0x1247e4) (andR32Imm8Effect 0x1247e4 4 12 0x7f)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1247e4 4 12 0x7f).toInstrSpec (and_r32_imm8_rex_effect_step 0x1247e4 0x41 0xe4 0x7f (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1247e8 [0x45, 0x09, 0xEC] (fun s => s.RIP = 0x1247e8) (orR32R32Effect 0x1247e8 3 12 13)
      [.gpr 12, .gpr 13] [] [.reg 12, .flags, .rip] :=
    (orR32R32Effect_footprint 0x1247e8 3 12 13).toInstrSpec (or_r32_r32_rex_effect_step 0x1247e8 0x45 0xec (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1247eb [0x84, 0xC0] (fun s => s.RIP = 0x1247eb) (testR8R8Effect 0x1247eb 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1247eb 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x1247eb 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1247d8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1247dd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1247e1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1247e4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1247e8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 63), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1247eb) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 63), (13, 53), (14, 14), (15, 15), (20, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1247ed) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 67) (jcc_rel32_effect_step 0x1247ed 9 0xffffff63) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1247d4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1247d4 :=
  Rest.liftedBlock (rest_l1247d4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1247d4 x hx)

theorem rest_l1247f3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1247f3 bytes_l1247f3) (entryMap (live .l1247f3))
      2 0x1247f3 bytes_l1247f3 b_l1247f3 := by
  have f0 : InstrSpec 0x1247f3 [0x41, 0x80, 0xFF, 0x0F] (fun s => s.RIP = 0x1247f3) (cmpR8Imm8Effect 0x1247f3 4 15 0xf)
      [.gpr 15] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x1247f3 4 15 0xf).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x1247f3 0x41 0xff 0xf (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1247f7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x1247f7 6 0x1b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1247f3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1247f3 :=
  Rest.liftedBlock (rest_l1247f3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1247f3 x hx)

theorem rest_l1247f9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1247f9 bytes_l1247f9) (entryMap (live .l1247f9))
      6 0x1247f9 bytes_l1247f9 b_l1247f9 := by
  have f0 : InstrSpec 0x1247f9 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x1247f9 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1247f9 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1247f9 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x1247f9 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x1247f9 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1247fe [0x41, 0x8B, 0x46, 0x1C] (LoadPre 0x1247fe (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1247fe + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1247fe 0 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR32M32Effect_footprint 0x1247fe 0 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x1247fe 0x41 (by decide) 0 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124802 [0xC7, 0x03, 0x01, 0x00, 0x00, 0x00] (StorePre 0x124802 6 (fun s => AddrMode.addr (.base 3 .none) s (0x124802 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124802 6 (.base 3 .none) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x124802 6 (.base 3 .none) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x124802 (.base 3 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x124808 [0x89, 0x43, 0x04] (StorePre 0x124808 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124808 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124808 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124808 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x124808 0 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12480b [0xC6, 0x43, 0x08, 0x10] (StorePre 0x12480b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12480b + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x12480b (.base 3 (.d8 0x8)) 0x10)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x12480b (.base 3 (.d8 0x8)) 0x10).toInstrSpec (mov_m8_imm8_effect_step 0x12480b (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide) 0x10) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1247fe) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124802) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124808) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12480b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12480f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x12480f 0x80 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1247f9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1247f9 :=
  Rest.liftedBlock (rest_l1247f9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1247f9 x hx)

theorem rest_l124814 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124814 bytes_l124814) (entryMap (live .l124814))
      4 0x124814 bytes_l124814 b_l124814 := by
  have f0 : InstrSpec 0x124814 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x124814) (movR64R64Effect 0x124814 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x124814 7 4).toInstrSpec (mov_r64_r64_effect_step 0x124814 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124817 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x124817) (movR64R64Effect 0x124817 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x124817 6 14).toInstrSpec (mov_r64_r64_effect_step 0x124817 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12481a [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12481a) (movR32Imm32Effect 0x12481a 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x12481a 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x12481a 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x12481f [0xE8, 0x5C, 0x33, 0x00, 0x00] (PushPre 0x12481f 5) (callEffect (fun _ => 0x127b80) 0x124824)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12481f 0x127b80 0x124824).toInstrSpec (call_rel32_effect_step 0x12481f 0x335c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124817) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12481a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12481f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l124814 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124814 :=
  Rest.liftedBlock (rest_l124814 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124814 x hx)

theorem rest_l124824 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124824 bytes_l124824) (entryMap (live .l124824))
      3 0x124824 bytes_l124824 b_l124824 := by
  have f0 : InstrSpec 0x124824 [0x8B, 0x04, 0x24] (LoadPre 0x124824 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124824 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124824 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x124824 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x124824 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124827 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x124827) (cmpR32Imm8Effect 0x124827 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124827 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124827 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124827) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12482a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x12482a 5 0x29) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124824 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124824 :=
  Rest.liftedBlock (rest_l124824 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124824 x hx)

theorem rest_l12482c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12482c bytes_l12482c) (entryMap (live .l12482c))
      3 0x12482c bytes_l12482c b_l12482c := by
  have f0 : InstrSpec 0x12482c [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x12482c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12482c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12482c 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12482c 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x12482c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124831 [0x48, 0x83, 0xFE, 0x01] (fun s => s.RIP = 0x124831) (cmpR64Imm8Effect 0x124831 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x124831 6 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x124831 0x48 0xfe 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124831) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124835) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x124835 5 0x6c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12482c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12482c :=
  Rest.liftedBlock (rest_l12482c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12482c x hx)

theorem rest_l124837 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124837 bytes_l124837) (entryMap (live .l124837))
      4 0x124837 bytes_l124837 b_l124837 := by
  have f0 : InstrSpec 0x124837 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x124837 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124837 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124837 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x124837 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x124837 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12483c [0x44, 0x0F, 0xB6, 0x38] (LoadPre 0x12483c (fun s => AddrMode.addr (.base 0 .none) s (0x12483c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x12483c 4 15 (.base 0 .none))
      [.gpr 0] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x12483c 4 15 (.base 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x12483c 0x44 (by decide) 7 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124840 [0x45, 0x84, 0xFF] (fun s => s.RIP = 0x124840) (testR8R8Effect 0x124840 3 15 15)
      [.gpr 15, .gpr 15] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x124840 3 15 15).toInstrSpec (test_r8_r8_rex_effect_step 0x124840 0x45 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12483c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124840) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 55), (20, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124843) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x124843 8 0xb4) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124837 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124837 :=
  Rest.liftedBlock (rest_l124837 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124837 x hx)

theorem rest_l124845 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124845 bytes_l124845) (entryMap (live .l124845))
      4 0x124845 bytes_l124845 b_l124845 := by
  have f0 : InstrSpec 0x124845 [0x41, 0xC1, 0xE4, 0x07] (fun s => s.RIP = 0x124845) (shlR32Effect 0x124845 4 12 7)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shlR32Effect_footprint 0x124845 4 12 7).toInstrSpec (shl_r32_imm8_rex_effect_step 0x124845 0x41 0xe4 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124849 [0x41, 0x83, 0xE7, 0x7F] (fun s => s.RIP = 0x124849) (andR32Imm8Effect 0x124849 4 15 0x7f)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x124849 4 15 0x7f).toInstrSpec (and_r32_imm8_rex_effect_step 0x124849 0x41 0xe7 0x7f (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12484d [0x45, 0x09, 0xE7] (fun s => s.RIP = 0x12484d) (orR32R32Effect 0x12484d 3 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (orR32R32Effect_footprint 0x12484d 3 15 12).toInstrSpec (or_r32_r32_rex_effect_step 0x12484d 0x45 0xe7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124849) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12484d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124850) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x124850 0xfffffe88 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124845 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124845 :=
  Rest.liftedBlock (rest_l124845 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124845 x hx)

theorem rest_l124855 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124855 bytes_l124855) (entryMap (live .l124855))
      15 0x124855 bytes_l124855 b_l124855 := by
  have f0 : InstrSpec 0x124855 [0x8B, 0x4C, 0x24, 0x04] (LoadPre 0x124855 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x124855 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124855 1 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x124855 1 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_low_effect_step 0x124855 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124859 [0x48, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x124859 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124859 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124859 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124859 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x124859 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12485e [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x12485e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12485e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12485e 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12485e 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x12485e 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x124863 [0x48, 0x8B, 0x7C, 0x24, 0x30] (LoadPre 0x124863 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x124863 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124863 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x124863 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x124863 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x124868 [0x48, 0x89, 0x7B, 0x30] (StorePre 0x124868 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x124868 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124868 7 (.base 3 (.d8 0x30)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124868 7 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x124868 0x48 (by decide) 7 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12486c [0x48, 0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x12486c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x12486c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12486c 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12486c 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x12486c 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x124871 [0x48, 0x89, 0x7B, 0x28] (StorePre 0x124871 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x124871 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124871 7 (.base 3 (.d8 0x28)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124871 7 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x124871 0x48 (by decide) 7 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x124875 [0x48, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x124875 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x124875 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124875 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x124875 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x124875 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x12487a [0x48, 0x89, 0x7B, 0x20] (StorePre 0x12487a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x12487a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12487a 7 (.base 3 (.d8 0x20)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12487a 7 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x12487a 0x48 (by decide) 7 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12487e [0x48, 0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x12487e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12487e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12487e 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12487e 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x12487e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x124883 [0x48, 0x89, 0x7B, 0x18] (StorePre 0x124883 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x124883 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124883 7 (.base 3 (.d8 0x18)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124883 7 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x124883 0x48 (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x124887 [0x89, 0x03] (StorePre 0x124887 2 (fun s => AddrMode.addr (.base 3 .none) s (0x124887 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x124887 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124887 0 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x124887 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x124889 [0x89, 0x4B, 0x04] (StorePre 0x124889 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124889 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124889 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124889 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x124889 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x12488c [0x48, 0x89, 0x53, 0x08] (StorePre 0x12488c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12488c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12488c 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12488c 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x12488c 0x48 (by decide) 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x124890 [0x48, 0x89, 0x73, 0x10] (StorePre 0x124890 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x124890 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124890 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124890 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x124890 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124859) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12485e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124863) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124868) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12486c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124871) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124875) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12487a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12487e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124883) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124887) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124889) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12488c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124890) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124894) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 75) (by decide) rfl

theorem block_l124855 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124855 :=
  Rest.liftedBlock (rest_l124855 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124855 x hx)

theorem rest_l124894 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124894 bytes_l124894) (entryMap (live .l124894))
      8 0x124894 bytes_l124894 b_l124894 := by
  have f0 : InstrSpec 0x124894 [0x48, 0x83, 0xC4, 0x38] (fun s => s.RIP = 0x124894) (addR64Imm8Effect 0x124894 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x124894 4 0x38).toInstrSpec (add_r64_imm8_effect_step 0x124894 0x48 0xc4 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124898 [0x5B] (PopPre 0x124898) (popR64Effect 0x124898 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124898 1 3).toInstrSpec (pop_r64_effect_step 0x124898 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x124899 [0x41, 0x5C] (PopPre 0x124899) (popR64Effect 0x124899 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124899 2 12).toInstrSpec (pop_r64_rex_effect_step 0x124899 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x12489b [0x41, 0x5D] (PopPre 0x12489b) (popR64Effect 0x12489b 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12489b 2 13).toInstrSpec (pop_r64_rex_effect_step 0x12489b 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x12489d [0x41, 0x5E] (PopPre 0x12489d) (popR64Effect 0x12489d 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12489d 2 14).toInstrSpec (pop_r64_rex_effect_step 0x12489d 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x12489f [0x41, 0x5F] (PopPre 0x12489f) (popR64Effect 0x12489f 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12489f 2 15).toInstrSpec (pop_r64_rex_effect_step 0x12489f 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1248a1 [0x5D] (PopPre 0x1248a1) (popR64Effect 0x1248a1 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1248a1 1 5).toInstrSpec (pop_r64_effect_step 0x1248a1 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1248a2 [0xC3] (RetPre 0x1248a2) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1248a2).toInstrSpec (ret_effect_step 0x1248a2) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124898) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124899) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12489b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12489d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12489f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1248a1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1248a2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l124894 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124894 :=
  Rest.liftedBlock (rest_l124894 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124894 x hx)

theorem rest_l1248a3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1248a3 bytes_l1248a3) (entryMap (live .l1248a3))
      3 0x1248a3 bytes_l1248a3 b_l1248a3 := by
  have f0 : InstrSpec 0x1248a3 [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1248a3) (movR32Imm32Effect 0x1248a3 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x1248a3 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1248a3 0xbf (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x1248a8 [0x48, 0xC7, 0xC2, 0xE0, 0x36, 0x20, 0x00] (fun s => s.RIP = 0x1248a8) (movR64Imm32Effect 0x1248a8 2 0x2036e0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x1248a8 2 0x2036e0).toInstrSpec (mov_r64_imm32_effect_step 0x1248a8 0x48 0xc2 (by decide) (by decide) (by decide) 0x2036e0) pre_rip
  have f2 : InstrSpec 0x1248af [0xE8, 0xDC, 0x53, 0x00, 0x00] (PushPre 0x1248af 5) (callEffect (fun _ => 0x129c90) 0x1248b4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1248af 0x129c90 0x1248b4).toInstrSpec (call_rel32_effect_step 0x1248af 0x53dc (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x1248a8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x1248af) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)]) (p' := 0x129c90) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l1248a3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1248a3 :=
  Rest.liftedBlock (rest_l1248a3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1248a3 x hx)

theorem rest_l1248b4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1248b4 bytes_l1248b4) (entryMap (live .l1248b4))
      2 0x1248b4 bytes_l1248b4 b_l1248b4 := by
  have f0 : InstrSpec 0x1248b4 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1248b4) (fun _ => nopEffect 0x1248b4 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1248b4 10).toInstrSpec (nop_m_effect_step 0x1248b4 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1248be [0x66, 0x90] (fun s => s.RIP = 0x1248be) (fun _ => nopEffect 0x1248be 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1248be 2).toInstrSpec (nop_66_effect_step 0x1248be) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1248be) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1248c0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1248b4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1248b4 :=
  Rest.liftedBlock (rest_l1248b4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1248b4 x hx)

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

theorem_by block_l124670_eval :
    program.runBlock (dialect code) ⟨.l124670, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124691_eval :
    program.runBlock (dialect code) ⟨.l124691, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1246a4_eval :
    program.runBlock (dialect code) ⟨.l1246a4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1246b0_eval :
    program.runBlock (dialect code) ⟨.l1246b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1246bf_eval :
    program.runBlock (dialect code) ⟨.l1246bf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1246d3_eval :
    program.runBlock (dialect code) ⟨.l1246d3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1246dd_eval :
    program.runBlock (dialect code) ⟨.l1246dd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1246eb_eval :
    program.runBlock (dialect code) ⟨.l1246eb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1246fa_eval :
    program.runBlock (dialect code) ⟨.l1246fa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124705_eval :
    program.runBlock (dialect code) ⟨.l124705, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12470e_eval :
    program.runBlock (dialect code) ⟨.l12470e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12471e_eval :
    program.runBlock (dialect code) ⟨.l12471e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12472a_eval :
    program.runBlock (dialect code) ⟨.l12472a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124739_eval :
    program.runBlock (dialect code) ⟨.l124739, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124756_eval :
    program.runBlock (dialect code) ⟨.l124756, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12475b_eval :
    program.runBlock (dialect code) ⟨.l12475b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12476b_eval :
    program.runBlock (dialect code) ⟨.l12476b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124777_eval :
    program.runBlock (dialect code) ⟨.l124777, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124786_eval :
    program.runBlock (dialect code) ⟨.l124786, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1247a1_eval :
    program.runBlock (dialect code) ⟨.l1247a1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1247a9_eval :
    program.runBlock (dialect code) ⟨.l1247a9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1247b9_eval :
    program.runBlock (dialect code) ⟨.l1247b9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1247c5_eval :
    program.runBlock (dialect code) ⟨.l1247c5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1247d4_eval :
    program.runBlock (dialect code) ⟨.l1247d4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1247f3_eval :
    program.runBlock (dialect code) ⟨.l1247f3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1247f9_eval :
    program.runBlock (dialect code) ⟨.l1247f9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124814_eval :
    program.runBlock (dialect code) ⟨.l124814, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124824_eval :
    program.runBlock (dialect code) ⟨.l124824, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12482c_eval :
    program.runBlock (dialect code) ⟨.l12482c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124837_eval :
    program.runBlock (dialect code) ⟨.l124837, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124845_eval :
    program.runBlock (dialect code) ⟨.l124845, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124855_eval :
    program.runBlock (dialect code) ⟨.l124855, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124894_eval :
    program.runBlock (dialect code) ⟨.l124894, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1248a3_eval :
    program.runBlock (dialect code) ⟨.l1248a3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1248b4_eval :
    program.runBlock (dialect code) ⟨.l1248b4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Ecdh.LIR
