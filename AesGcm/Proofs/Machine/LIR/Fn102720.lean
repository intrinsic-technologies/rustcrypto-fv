import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l102720 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102720 bytes_l102720) (entryMap (live .l102720))
      17 0x102720 bytes_l102720 b_l102720 := by
  have f0 : InstrSpec 0x102720 [0x55] (PushPre 0x102720 1) (pushR64Effect 0x102720 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102720 1 5).toInstrSpec (push_r64_effect_step 0x102720 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x102721 [0x41, 0x57] (PushPre 0x102721 2) (pushR64Effect 0x102721 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102721 2 15).toInstrSpec (push_r64_rex_effect_step 0x102721 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x102723 [0x41, 0x56] (PushPre 0x102723 2) (pushR64Effect 0x102723 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102723 2 14).toInstrSpec (push_r64_rex_effect_step 0x102723 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x102725 [0x41, 0x55] (PushPre 0x102725 2) (pushR64Effect 0x102725 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102725 2 13).toInstrSpec (push_r64_rex_effect_step 0x102725 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x102727 [0x41, 0x54] (PushPre 0x102727 2) (pushR64Effect 0x102727 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102727 2 12).toInstrSpec (push_r64_rex_effect_step 0x102727 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x102729 [0x53] (PushPre 0x102729 1) (pushR64Effect 0x102729 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102729 1 3).toInstrSpec (push_r64_effect_step 0x102729 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10272a [0x48, 0x81, 0xEC, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10272a) (subR64Imm32Effect 0x10272a 4 0xa8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10272a 4 0xa8).toInstrSpec (sub_r64_imm32_effect_step 0x10272a 0x48 0xec 0xa8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x102731 [0x48, 0x89, 0xCD] (fun s => s.RIP = 0x102731) (movR64R64Effect 0x102731 5 1)
      [.gpr 1] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x102731 5 1).toInstrSpec (mov_r64_r64_effect_step 0x102731 0x48 0xcd (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x102734 [0x48, 0xBB, 0xE0, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102734) (movR64Imm64Effect 0x102734 3 0xfffffffe0)
      [] [] [.reg 3, .rip] :=
    (movR64Imm64Effect_footprint 0x102734 3 0xfffffffe0).toInstrSpec (mov_r64_imm64_effect_step 0x102734 0x48 0xbb (by decide) (by decide) 0xfffffffe0) pre_rip
  have f9 : InstrSpec 0x10273e [0x4D, 0x8B, 0x70, 0x10] (LoadPre 0x10273e (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x10273e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10273e 14 (.base 8 (.d8 0x10)))
      [.gpr 8] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x10273e 14 (.base 8 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10273e 0x4d (by decide) 6 (.base 8 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x102742 [0x49, 0x39, 0xDE] (fun s => s.RIP = 0x102742) (cmpR64R64Effect 0x102742 14 3)
      [.gpr 14, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x102742 14 3).toInstrSpec (cmp_r64_r64_effect_step 0x102742 0x49 0xde (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x102745 [0x0F, 0x97, 0xC0] (fun s => s.RIP = 0x102745) (atFlags (condHolds 7) (setccR8Effect 0x102745 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x102745 3 0 7).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x102745 7 0xc0 (by decide) (by decide) c)) pre_rip
  have f12 : InstrSpec 0x102748 [0x48, 0xC1, 0xE9, 0x3D] (fun s => s.RIP = 0x102748) (shrR64Effect 0x102748 4 1 61)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x102748 4 1 61).toInstrSpec (shr_r64_imm8_effect_step 0x102748 0x48 0xe9 0x3d (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10274c [0x0F, 0x95, 0xC1] (fun s => s.RIP = 0x10274c) (atFlags (condHolds 5) (setccR8Effect 0x10274c 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x10274c 3 1 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x10274c 5 0xc1 (by decide) (by decide) c)) pre_rip
  have f14 : InstrSpec 0x10274f [0x08, 0xC1] (fun s => s.RIP = 0x10274f) (orR8R8Effect 0x10274f 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR8R8Effect_footprint 0x10274f 2 1 0).toInstrSpec (or_r8_r8_effect_step 0x10274f 0xc1 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x102751 [0xB0, 0x01] (fun s => s.RIP = 0x102751) (movR8Imm8Effect 0x102751 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x102751 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x102751 0xb0 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102721) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102723) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102725) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102727) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102729) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10272a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102731) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102734) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10273e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102742) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (16, 73), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102745) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 1), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (16, 73), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102748) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 79) f12 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x102748 4 1 61 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 80) (ρ' := [(0, 76), (1, 78), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (19, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10274c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 76), (1, 81), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (19, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10274f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 84) f14 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 85) (ρ' := [(0, 76), (1, 83), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (19, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102751) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 86), (1, 83), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (19, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102753) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 88) (jcc_rel32_effect_step 0x102753 5 0x208) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102720 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102720 :=
  Rest.liftedBlock (rest_l102720 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102720 x hx)

theorem rest_l102759_1 [Bindings] (code : CodeMap) :
    Rest (n := 82) code lifted (codeRange 0x102759 bytes_l102759) [(0, 57), (1, 59), (2, 77), (3, 3), (4, 4), (5, 5), (6, 66), (7, 75), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x1027b7 bytes_l102759_1 b_l102759_1 := by
  have f20 : InstrSpec 0x1027b7 [0xE8, 0xA4, 0x41, 0x00, 0x00] (PushPre 0x1027b7 5) (callEffect (fun _ => 0x106960) 0x1027bc)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1027b7 0x106960 0x1027bc).toInstrSpec (call_rel32_effect_step 0x1027b7 0x41a4 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 57), (1, 59), (2, 77), (3, 3), (4, 82), (5, 5), (6, 66), (7, 75), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106960) f20 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 84) (by decide) (by decide) rfl rfl

theorem rest_l102759 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102759 bytes_l102759) (entryMap (live .l102759))
      21 0x102759 bytes_l102759 b_l102759 := by
  have f0 : InstrSpec 0x102759 [0x4D, 0x89, 0xCD] (fun s => s.RIP = 0x102759) (movR64R64Effect 0x102759 13 9)
      [.gpr 9] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x102759 13 9).toInstrSpec (mov_r64_r64_effect_step 0x102759 0x4d 0xcd (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10275c [0x49, 0x89, 0xFC] (fun s => s.RIP = 0x10275c) (movR64R64Effect 0x10275c 12 7)
      [.gpr 7] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10275c 12 7).toInstrSpec (mov_r64_r64_effect_step 0x10275c 0x49 0xfc (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10275f [0x8B, 0x06] (LoadPre 0x10275f (fun s => AddrMode.addr (.base 6 .none) s (0x10275f + BitVec.ofNat 64 2)) 4) (movR32M32LowEffect 0x10275f 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x10275f 0 (.base 6 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x10275f 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x102761 [0x8B, 0x4E, 0x04] (LoadPre 0x102761 (fun s => AddrMode.addr (.base 6 (.d8 0x4)) s (0x102761 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x102761 1 (.base 6 (.d8 0x4)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x102761 1 (.base 6 (.d8 0x4))).toInstrSpec (mov_r32_m32_low_effect_step 0x102761 1 (.base 6 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x102764 [0x48, 0x89, 0x54, 0x24, 0x50] (StorePre 0x102764 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x102764 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102764 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102764 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x102764 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x102769 [0x8B, 0x56, 0x08] (LoadPre 0x102769 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x102769 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x102769 2 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x102769 2 (.base 6 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x102769 2 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10276c [0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10276c 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10276c + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10276c (.sib 4 none 0 (.d32 0x80)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10276c (.sib 4 none 0 (.d32 0x80)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10276c 0x48 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x102778 [0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102778 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x102778 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102778 (.sib 4 none 0 (.d8 0x78)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102778 (.sib 4 none 0 (.d8 0x78)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102778 0x48 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x102781 [0x48, 0x8D, 0x77, 0x20] (fun s => s.RIP = 0x102781) (leaR64Effect 0x102781 6 (.base 7 (.d8 0x20)))
      [.gpr 7] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102781 6 (.base 7 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x102781 0x48 (by decide) 6 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x102785 [0x89, 0x44, 0x24, 0x3C] (StorePre 0x102785 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x102785 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102785 0 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x102785 0 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_m32_r32_low_effect_step 0x102785 0 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x102789 [0x89, 0x44, 0x24, 0x10] (StorePre 0x102789 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102789 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102789 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x102789 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m32_r32_low_effect_step 0x102789 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x10278d [0x89, 0x4C, 0x24, 0x38] (StorePre 0x10278d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10278d + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10278d 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10278d 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m32_r32_low_effect_step 0x10278d 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x102791 [0x89, 0x4C, 0x24, 0x14] (StorePre 0x102791 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x102791 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102791 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x102791 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m32_r32_low_effect_step 0x102791 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x102795 [0x89, 0x54, 0x24, 0x34] (StorePre 0x102795 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x102795 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102795 2 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x102795 2 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x102795 2 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x102799 [0x89, 0x54, 0x24, 0x18] (StorePre 0x102799 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102799 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102799 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x102799 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m32_r32_low_effect_step 0x102799 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x10279d [0xC7, 0x44, 0x24, 0x1C, 0x00, 0x00, 0x00, 0x01] (StorePre 0x10279d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10279d + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x10279d 8 (.sib 4 none 0 (.d8 0x1c)) 0x1000000)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x10279d 8 (.sib 4 none 0 (.d8 0x1c)) 0x1000000).toInstrSpec (mov_m32_imm32_effect_step 0x10279d (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide) 0x1000000) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x1027a5 [0x48, 0x8D, 0x7C, 0x24, 0x78] (fun s => s.RIP = 0x1027a5) (leaR64Effect 0x1027a5 7 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1027a5 7 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x1027a5 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1027aa [0x48, 0x8D, 0x54, 0x24, 0x10] (fun s => s.RIP = 0x1027aa) (leaR64Effect 0x1027aa 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1027aa 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1027aa 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1027af [0x48, 0x89, 0x74, 0x24, 0x48] (StorePre 0x1027af 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1027af + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1027af 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1027af 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x1027af 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1027b4 [0x4D, 0x89, 0xC7] (fun s => s.RIP = 0x1027b4) (movR64R64Effect 0x1027b4 15 8)
      [.gpr 8] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1027b4 15 8).toInstrSpec (mov_r64_r64_effect_step 0x1027b4 0x4d 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10275c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10275f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102761) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102764) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102769) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10276c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102778) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102781) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102785) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102789) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10278d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102791) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102795) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102799) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10279d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027a5) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 75), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027aa) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 57), (1, 59), (2, 77), (3, 3), (4, 4), (5, 5), (6, 66), (7, 75), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027af) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 57), (1, 59), (2, 77), (3, 3), (4, 4), (5, 5), (6, 66), (7, 75), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027b4) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f19 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 57), (1, 59), (2, 77), (3, 3), (4, 4), (5, 5), (6, 66), (7, 75), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027b7) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102759_1 code

theorem block_l102759 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102759 :=
  Rest.liftedBlock (rest_l102759 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102759 x hx)

theorem rest_l1027bc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1027bc bytes_l1027bc) (entryMap (live .l1027bc))
      10 0x1027bc bytes_l1027bc b_l1027bc := by
  have f0 : InstrSpec 0x1027bc [0x4C, 0x89, 0x7C, 0x24, 0x40] (StorePre 0x1027bc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1027bc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1027bc 15 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1027bc 15 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x1027bc 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1027c1 [0x4D, 0x8B, 0x0F] (LoadPre 0x1027c1 (fun s => AddrMode.addr (.base 15 .none) s (0x1027c1 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1027c1 9 (.base 15 .none))
      [.gpr 15] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1027c1 9 (.base 15 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1027c1 0x4d (by decide) 1 (.base 15 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1027c4 [0x4C, 0x89, 0x34, 0x24] (StorePre 0x1027c4 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1027c4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1027c4 14 (.sib 4 none 0 .none))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1027c4 14 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1027c4 0x4c (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1027c8 [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1027c8) (leaR64Effect 0x1027c8 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1027c8 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x1027c8 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1027d0 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x1027d0) (movR64R64Effect 0x1027d0 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1027d0 6 12).toInstrSpec (mov_r64_r64_effect_step 0x1027d0 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1027d3 [0x48, 0x8D, 0x54, 0x24, 0x78] (fun s => s.RIP = 0x1027d3) (leaR64Effect 0x1027d3 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1027d3 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x1027d3 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1027d8 [0x48, 0x8B, 0x4C, 0x24, 0x50] (LoadPre 0x1027d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1027d8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1027d8 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1027d8 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x1027d8 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1027dd [0x49, 0x89, 0xE8] (fun s => s.RIP = 0x1027dd) (movR64R64Effect 0x1027dd 8 5)
      [.gpr 5] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1027dd 8 5).toInstrSpec (mov_r64_r64_effect_step 0x1027dd 0x49 0xe8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1027e0 [0x4D, 0x89, 0xCC] (fun s => s.RIP = 0x1027e0) (movR64R64Effect 0x1027e0 12 9)
      [.gpr 9] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x1027e0 12 9).toInstrSpec (mov_r64_r64_effect_step 0x1027e0 0x4d 0xcc (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1027e3 [0xE8, 0x38, 0xF4, 0xFF, 0xFF] (PushPre 0x1027e3 5) (callEffect (fun _ => 0x101c20) 0x1027e8)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1027e3 0x101c20 0x1027e8).toInstrSpec (call_rel32_effect_step 0x1027e3 0xfffff438 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 54), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027c4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 54), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027c8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 57), (9, 54), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027d0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 54), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027d3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 54), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027d8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 63), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 54), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027dd) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 63), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (8, 65), (9, 54), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027e0) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 63), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (8, 65), (9, 54), (11, 11), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027e3) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 63), (2, 61), (3, 3), (4, 69), (5, 5), (6, 59), (7, 57), (8, 65), (9, 54), (11, 11), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c20) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l1027bc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1027bc :=
  Rest.liftedBlock (rest_l1027bc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1027bc x hx)

theorem rest_l1027e8_1 [Bindings] (code : CodeMap) :
    Rest (n := 95) code lifted (codeRange 0x1027e8 bytes_l1027e8) [(0, 92), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x102836 bytes_l1027e8_1 b_l1027e8_1 := by
  have f20 : InstrSpec 0x102836 [0x48, 0x8D, 0x44, 0x24, 0x10] (fun s => s.RIP = 0x102836) (leaR64Effect 0x102836 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x102836 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x102836 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x10283b [0x80, 0x7C, 0x24, 0x10, 0x00] (LoadPre 0x10283b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10283b + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x10283b 5 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x10283b 5 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x10283b (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x102840 [0x0F, 0x94, 0xC0] (fun s => s.RIP = 0x102840) (atFlags (condHolds 4) (setccR8Effect 0x102840 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x102840 3 0 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x102840 4 0xc0 (by decide) (by decide) c)) pre_rip
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10283b) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f21 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 95), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102840) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 99), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102843) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 101) (jcc_rel32_effect_step 0x102843 4 0x118) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l1027e8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1027e8 bytes_l1027e8) (entryMap (live .l1027e8))
      24 0x1027e8 bytes_l1027e8 b_l1027e8 := by
  have f0 : InstrSpec 0x1027e8 [0x48, 0x8B, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x1027e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1027e8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1027e8 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1027e8 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x1027e8 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1027f0 [0x48, 0x8B, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x1027f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1027f0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1027f0 6 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1027f0 6 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x1027f0 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1027f8 [0x49, 0x8B, 0x7D, 0x00] (LoadPre 0x1027f8 (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x1027f8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1027f8 7 (.base 13 (.d8 0x0)))
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1027f8 7 (.base 13 (.d8 0x0))).toInstrSpec (mov_r64_m64_effect_step 0x1027f8 0x49 (by decide) 7 (.base 13 (.d8 0x0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1027fc [0x4D, 0x8B, 0x45, 0x08] (LoadPre 0x1027fc (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x1027fc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1027fc 8 (.base 13 (.d8 0x8)))
      [.gpr 13] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1027fc 8 (.base 13 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1027fc 0x4d (by decide) 0 (.base 13 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x102800 [0x31, 0xC0] (fun s => s.RIP = 0x102800) (xorR32R32Effect 0x102800 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x102800 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x102800 0xc0 (by decide)) pre_rip
  have f5 : InstrSpec 0x102802 [0x66, 0xB9, 0x01, 0x00] (fun s => s.RIP = 0x102802) (movR16Imm16Effect 0x102802 4 1 0x1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR16Imm16Effect_footprint 0x102802 4 1 0x1).toInstrSpec (mov_r16_imm16_effect_step 0x102802 0xb9 (by decide) 0x1) pre_rip
  have f6 : InstrSpec 0x102806 [0x66, 0x41, 0xB9, 0x01, 0x00] (fun s => s.RIP = 0x102806) (movR16Imm16Effect 0x102806 5 9 0x1)
      [.gpr 9] [] [.reg 9, .rip] :=
    (movR16Imm16Effect_footprint 0x102806 5 9 0x1).toInstrSpec (mov_r16_imm16_rex_effect_step 0x102806 0x41 (by decide) 0xb9 (by decide) 0x1) pre_rip
  have f7 : InstrSpec 0x10280b [0x48, 0x31, 0xFA] (fun s => s.RIP = 0x10280b) (xorR64R64Effect 0x10280b 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10280b 2 7).toInstrSpec (xor_r64_r64_effect_step 0x10280b 0x48 0xfa (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10280e [0x4C, 0x0F, 0x45, 0xC8] (fun s => s.RIP = 0x10280e) (atFlags (condHolds 5) (cmovR64R64Effect 0x10280e 4 9 0))
      [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 9, .rip] :=
    (cmovR64R64Effect_footprint 0x10280e 4 9 0 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10280e 5 0x4c (by decide) 0xc8 (by decide) c)) pre_rip
  have f9 : InstrSpec 0x102812 [0x41, 0x0F, 0xB6, 0xD1] (fun s => s.RIP = 0x102812) (movzxR32R8Effect 0x102812 4 2 9)
      [.gpr 9] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x102812 4 2 9).toInstrSpec (movzx_r32_r8_rex_effect_step 0x102812 0x41 (by decide) 0xd1 (by decide)) pre_rip
  have f10 : InstrSpec 0x102816 [0x4C, 0x31, 0xC6] (fun s => s.RIP = 0x102816) (xorR64R64Effect 0x102816 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102816 6 8).toInstrSpec (xor_r64_r64_effect_step 0x102816 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x102819 [0x48, 0x0F, 0x45, 0xD0] (fun s => s.RIP = 0x102819) (atFlags (condHolds 5) (cmovR64R64Effect 0x102819 4 2 0))
      [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x102819 4 2 0 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x102819 5 0x48 (by decide) 0xd0 (by decide) c)) pre_rip
  have f12 : InstrSpec 0x10281d [0x0F, 0xB6, 0xD2] (fun s => s.RIP = 0x10281d) (movzxR32R8Effect 0x10281d 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x10281d 3 2 2).toInstrSpec (movzx_r32_r8_effect_step 0x10281d 0xd2 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x102820 [0x31, 0xF6] (fun s => s.RIP = 0x102820) (xorR32R32Effect 0x102820 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x102820 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x102820 0xf6 (by decide)) pre_rip
  have f14 : InstrSpec 0x102822 [0x48, 0x31, 0xC6] (fun s => s.RIP = 0x102822) (xorR64R64Effect 0x102822 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102822 6 0).toInstrSpec (xor_r64_r64_effect_step 0x102822 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x102825 [0x48, 0x0F, 0x45, 0xD0] (fun s => s.RIP = 0x102825) (atFlags (condHolds 5) (cmovR64R64Effect 0x102825 4 2 0))
      [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x102825 4 2 0 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x102825 5 0x48 (by decide) 0xd0 (by decide) c)) pre_rip
  have f16 : InstrSpec 0x102829 [0x0F, 0xB6, 0xD2] (fun s => s.RIP = 0x102829) (movzxR32R8Effect 0x102829 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x102829 3 2 2).toInstrSpec (movzx_r32_r8_effect_step 0x102829 0xd2 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10282c [0x66, 0x31, 0xCA] (fun s => s.RIP = 0x10282c) (xorR16R16Effect 0x10282c 3 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR16R16Effect_footprint 0x10282c 3 2 1).toInstrSpec (xor_r16_r16_effect_step 0x10282c 0xca (by decide)) pre_rip
  have f18 : InstrSpec 0x10282f [0x0F, 0x44, 0xC1] (fun s => s.RIP = 0x10282f) (atFlags (condHolds 4) (cmovR32R32Effect 0x10282f 3 0 1))
      [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (cmovR32R32Effect_footprint 0x10282f 3 0 1 4).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_effect_step 0x10282f 4 0xc1 (by decide) c)) pre_rip
  have f19 : InstrSpec 0x102832 [0x88, 0x44, 0x24, 0x10] (StorePre 0x102832 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102832 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x102832 4 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x102832 4 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x102832 0 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027f0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027f8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1027fc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102800) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102802) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102806) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 63), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 65), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10280b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 65), (11, 11), (12, 12), (13, 13), (14, 14), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10280e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102812) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 61), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102816) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 61), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 73), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102819) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 61), (1, 63), (2, 76), (3, 3), (4, 4), (5, 5), (6, 73), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10281d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 61), (1, 63), (2, 78), (3, 3), (4, 4), (5, 5), (6, 73), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102820) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 61), (1, 63), (2, 78), (3, 3), (4, 4), (5, 5), (6, 80), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102822) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f14 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 61), (1, 63), (2, 78), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102825) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 61), (1, 63), (2, 85), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102829) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 61), (1, 63), (2, 87), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10282c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 90) f17 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 91) (ρ' := [(0, 61), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10282f) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 92), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102832) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 92), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102836) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1027e8_1 code

theorem block_l1027e8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1027e8 :=
  Rest.liftedBlock (rest_l1027e8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1027e8 x hx)

theorem rest_l102849 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102849 bytes_l102849) (entryMap (live .l102849))
      13 0x102849 bytes_l102849 b_l102849 := by
  have f0 : InstrSpec 0x102849 [0x48, 0x8B, 0x4C, 0x24, 0x48] (LoadPre 0x102849 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x102849 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102849 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x102849 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x102849 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10284e [0x48, 0x89, 0x4C, 0x24, 0x58] (StorePre 0x10284e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10284e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10284e 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10284e 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x10284e 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x102853 [0x4C, 0x8D, 0x7C, 0x24, 0x60] (fun s => s.RIP = 0x102853) (leaR64Effect 0x102853 15 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x102853 15 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (lea_r64_effect_step 0x102853 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102858 [0x8B, 0x4C, 0x24, 0x3C] (LoadPre 0x102858 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x102858 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x102858 1 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x102858 1 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r32_m32_low_effect_step 0x102858 1 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10285c [0x89, 0x4C, 0x24, 0x60] (StorePre 0x10285c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10285c + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10285c 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10285c 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m32_r32_low_effect_step 0x10285c 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x102860 [0x8B, 0x4C, 0x24, 0x38] (LoadPre 0x102860 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x102860 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x102860 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x102860 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r32_m32_low_effect_step 0x102860 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x102864 [0x89, 0x4C, 0x24, 0x64] (StorePre 0x102864 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x102864 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102864 1 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x102864 1 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (mov_m32_r32_low_effect_step 0x102864 1 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x102868 [0x8B, 0x4C, 0x24, 0x34] (LoadPre 0x102868 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x102868 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x102868 1 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x102868 1 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r32_m32_low_effect_step 0x102868 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10286c [0x89, 0x4C, 0x24, 0x68] (StorePre 0x10286c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10286c + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10286c 1 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10286c 1 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m32_r32_low_effect_step 0x10286c 1 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x102870 [0x48, 0xB9, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102870) (movR64Imm64Effect 0x102870 1 0x100000001)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x102870 1 0x100000001).toInstrSpec (mov_r64_imm64_effect_step 0x102870 0x48 0xb9 (by decide) (by decide) 0x100000001) pre_rip
  have f10 : InstrSpec 0x10287a [0x48, 0x89, 0x4C, 0x24, 0x6C] (StorePre 0x10287a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x10287a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10287a 1 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10287a 1 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (mov_m64_r64_effect_step 0x10287a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x10287f [0x49, 0x83, 0xFE, 0x11] (fun s => s.RIP = 0x10287f) (cmpR64Imm8Effect 0x10287f 14 0x11)
      [.gpr 14] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x10287f 14 0x11).toInstrSpec (cmp_r64_imm8_effect_step 0x10287f 0x49 0xfe 0x11 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10284e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102853) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102858) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 58), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10285c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 58), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102860) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102864) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102868) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10286c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102870) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10287a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10287f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (16, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102883) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 72) (jcc_rel8_effect_step 0x102883 2 0x57) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102849 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102849 :=
  Rest.liftedBlock (rest_l102849 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102849 x hx)

theorem rest_l102885 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102885 bytes_l102885) (entryMap (live .l102885))
      18 0x102885 bytes_l102885 b_l102885 := by
  have f0 : InstrSpec 0x102885 [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x102885) (movR64R64Effect 0x102885 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102885 1 14).toInstrSpec (mov_r64_r64_effect_step 0x102885 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102888 [0x48, 0xC1, 0xE9, 0x04] (fun s => s.RIP = 0x102888) (shrR64Effect 0x102888 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x102888 4 1 4).toInstrSpec (shr_r64_imm8_effect_step 0x102888 0x48 0xe9 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10288c [0x48, 0x8B, 0x74, 0x24, 0x40] (LoadPre 0x10288c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10288c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10288c 6 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10288c 6 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10288c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x102891 [0x48, 0x8B, 0x56, 0x08] (LoadPre 0x102891 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x102891 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102891 2 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x102891 2 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x102891 0x48 (by decide) 2 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x102895 [0x48, 0x83, 0xC3, 0x10] (fun s => s.RIP = 0x102895) (addR64Imm8Effect 0x102895 3 0x10)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x102895 3 0x10).toInstrSpec (add_r64_imm8_effect_step 0x102895 0x48 0xc3 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x102899 [0x4C, 0x21, 0xF3] (fun s => s.RIP = 0x102899) (andR64R64Effect 0x102899 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102899 3 14).toInstrSpec (and_r64_r64_effect_step 0x102899 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10289c [0x41, 0x83, 0xE6, 0x0F] (fun s => s.RIP = 0x10289c) (andR32Imm8Effect 0x10289c 4 14 0xf)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x10289c 4 14 0xf).toInstrSpec (and_r32_imm8_rex_effect_step 0x10289c 0x41 0xe6 0xf (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1028a0 [0x4D, 0x8D, 0x2C, 0x1C] (fun s => s.RIP = 0x1028a0) (leaR64Effect 0x1028a0 13 (.sib 12 (some 3) 0 .none))
      [.gpr 12, .gpr 3] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x1028a0 13 (.sib 12 (some 3) 0 .none)).toInstrSpec (lea_r64_effect_step 0x1028a0 0x4d (by decide) 5 (.sib 12 (some 3) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1028a4 [0x48, 0x01, 0xD3] (fun s => s.RIP = 0x1028a4) (addR64R64Effect 0x1028a4 3 2)
      [.gpr 3, .gpr 2] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1028a4 3 2).toInstrSpec (add_r64_r64_effect_step 0x1028a4 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1028a7 [0x48, 0x89, 0x5E, 0x08] (StorePre 0x1028a7 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1028a7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1028a7 3 (.base 6 (.d8 0x8)))
      [.gpr 3, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x1028a7 3 (.base 6 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1028a7 0x48 (by decide) 3 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1028ab [0x4C, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x1028ab 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1028ab + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1028ab 15 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1028ab 15 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1028ab 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1028b0 [0x4C, 0x89, 0x64, 0x24, 0x18] (StorePre 0x1028b0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1028b0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1028b0 12 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1028b0 12 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1028b0 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1028b5 [0x48, 0x89, 0x54, 0x24, 0x20] (StorePre 0x1028b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1028b5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1028b5 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1028b5 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1028b5 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1028ba [0x48, 0x89, 0x4C, 0x24, 0x28] (StorePre 0x1028ba 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1028ba + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1028ba 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1028ba 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1028ba 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1028bf [0x48, 0x8D, 0x7C, 0x24, 0x58] (fun s => s.RIP = 0x1028bf) (leaR64Effect 0x1028bf 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1028bf 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (lea_r64_effect_step 0x1028bf 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1028c4 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x1028c4) (leaR64Effect 0x1028c4 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1028c4 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1028c4 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1028c9 [0x89, 0xC3] (fun s => s.RIP = 0x1028c9) (movR32R32Effect 0x1028c9 2 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x1028c9 2 3 0).toInstrSpec (mov_r32_r32_effect_step 0x1028c9 0xc3 (by decide)) pre_rip
  have f17 : InstrSpec 0x1028cb [0xE8, 0x10, 0x5C, 0x00, 0x00] (PushPre 0x1028cb 5) (callEffect (fun _ => 0x1084e0) 0x1028d0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1028cb 0x1084e0 0x1028d0).toInstrSpec (call_rel32_effect_step 0x1028cb 0x5c10 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102888) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10288c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102891) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102895) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 61), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102899) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 63), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10289c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 63), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028a0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 63), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028a4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 69), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028a7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 69), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028ab) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 69), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028b0) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 69), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028b5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 69), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028ba) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 69), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028bf) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 69), (4, 4), (5, 5), (6, 57), (7, 76), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028c4) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 69), (4, 4), (5, 5), (6, 78), (7, 76), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028c9) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 80), (4, 4), (5, 5), (6, 78), (7, 76), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028cb) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f17 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 80), (4, 82), (5, 5), (6, 78), (7, 76), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084e0) f17 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 84) (by decide) (by decide) rfl rfl

theorem block_l102885 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102885 :=
  Rest.liftedBlock (rest_l102885 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102885 x hx)

theorem rest_l1028d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1028d0 bytes_l1028d0) (entryMap (live .l1028d0))
      3 0x1028d0 bytes_l1028d0 b_l1028d0 := by
  have f0 : InstrSpec 0x1028d0 [0x89, 0xD8] (fun s => s.RIP = 0x1028d0) (movR32R32Effect 0x1028d0 2 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1028d0 2 0 3).toInstrSpec (mov_r32_r32_effect_step 0x1028d0 0xd8 (by decide)) pre_rip
  have f1 : InstrSpec 0x1028d2 [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x1028d2) (testR64R64Effect 0x1028d2 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1028d2 14 14).toInstrSpec (test_r64_r64_effect_step 0x1028d2 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028d2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028d5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1028d5 5 0xd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1028d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1028d0 :=
  Rest.liftedBlock (rest_l1028d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1028d0 x hx)

theorem rest_l1028d7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1028d7 bytes_l1028d7) (entryMap (live .l1028d7))
      1 0x1028d7 bytes_l1028d7 b_l1028d7 := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x1028d7 0x85 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1028d7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1028d7 :=
  Rest.liftedBlock (rest_l1028d7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1028d7 x hx)

theorem rest_l1028dc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1028dc bytes_l1028dc) (entryMap (live .l1028dc))
      3 0x1028dc bytes_l1028dc b_l1028dc := by
  have f0 : InstrSpec 0x1028dc [0x4D, 0x89, 0xE5] (fun s => s.RIP = 0x1028dc) (movR64R64Effect 0x1028dc 13 12)
      [.gpr 12] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1028dc 13 12).toInstrSpec (mov_r64_r64_effect_step 0x1028dc 0x4d 0xe5 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1028df [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x1028df) (testR64R64Effect 0x1028df 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1028df 14 14).toInstrSpec (test_r64_r64_effect_step 0x1028df 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028df) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028e2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1028e2 4 0x7d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1028dc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1028dc :=
  Rest.liftedBlock (rest_l1028dc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1028dc x hx)

theorem rest_l1028e4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1028e4 bytes_l1028e4) (entryMap (live .l1028e4))
      10 0x1028e4 bytes_l1028e4 b_l1028e4 := by
  have f0 : InstrSpec 0x1028e4 [0xB9, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1028e4) (movR32Imm32Effect 0x1028e4 5 1 0x10)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1028e4 5 1 0x10).toInstrSpec (mov_r32_imm32_effect_step 0x1028e4 0xb9 (by decide) 0x10) pre_rip
  have f1 : InstrSpec 0x1028e9 [0x4C, 0x29, 0xF1] (fun s => s.RIP = 0x1028e9) (subR64R64Effect 0x1028e9 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1028e9 1 14).toInstrSpec (sub_r64_r64_effect_step 0x1028e9 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1028ec [0x31, 0xD2] (fun s => s.RIP = 0x1028ec) (xorR32R32Effect 0x1028ec 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1028ec 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x1028ec 0xd2 (by decide)) pre_rip
  have f3 : InstrSpec 0x1028ee [0x49, 0x83, 0xFE, 0x10] (fun s => s.RIP = 0x1028ee) (cmpR64Imm8Effect 0x1028ee 14 0x10)
      [.gpr 14] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1028ee 14 0x10).toInstrSpec (cmp_r64_imm8_effect_step 0x1028ee 0x49 0xfe 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1028f2 [0x48, 0x0F, 0x42, 0xD1] (fun s => s.RIP = 0x1028f2) (atFlags (condHolds 2) (cmovR64R64Effect 0x1028f2 4 2 1))
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x1028f2 4 2 1 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x1028f2 2 0x48 (by decide) 0xd1 (by decide) c)) pre_rip
  have f5 : InstrSpec 0x1028f6 [0x4A, 0x8D, 0x3C, 0x34] (fun s => s.RIP = 0x1028f6) (leaR64Effect 0x1028f6 7 (.sib 4 (some 14) 0 .none))
      [.gpr 4, .gpr 14] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1028f6 7 (.sib 4 (some 14) 0 .none)).toInstrSpec (lea_r64_effect_step 0x1028f6 0x4a (by decide) 7 (.sib 4 (some 14) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1028fa [0x48, 0x81, 0xC7, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1028fa) (addR64Imm32Effect 0x1028fa 7 0x98)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x1028fa 7 0x98).toInstrSpec (add_r64_imm32_effect_step 0x1028fa 0x48 0xc7 0x98 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x102901 [0x31, 0xF6] (fun s => s.RIP = 0x102901) (xorR32R32Effect 0x102901 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x102901 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x102901 0xf6 (by decide)) pre_rip
  have f8 : InstrSpec 0x102903 [0x89, 0xC5] (fun s => s.RIP = 0x102903) (movR32R32Effect 0x102903 2 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x102903 2 5 0).toInstrSpec (mov_r32_r32_effect_step 0x102903 0xc5 (by decide)) pre_rip
  have f9 : InstrSpec 0x102905 [0xFF, 0x15, 0x1D, 0xE9, 0x0F, 0x00] (GoesTo (CallMemPre 0x102905 (.rip 0xfe91d)) (callEffect (callMemPtr 0x102905 (.rip 0xfe91d)) (0x102905 + BitVec.ofNat 64 (callMemLen (.rip 0xfe91d)))) 0x103eb0) (callEffect (callMemPtr 0x102905 (.rip 0xfe91d)) (0x102905 + BitVec.ofNat 64 (callMemLen (.rip 0xfe91d))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x102905 (.rip 0xfe91d)).toInstrSpec (call_m64_effect_step 0x102905 (.rip 0xfe91d) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103eb0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028e9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028ec) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028ee) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028f2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 61), (3, 3), (4, 4), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028f6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 61), (3, 3), (4, 4), (6, 6), (7, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1028fa) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 61), (3, 3), (4, 4), (6, 6), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102901) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 55), (2, 61), (3, 3), (4, 4), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102903) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 55), (2, 61), (3, 3), (4, 4), (5, 69), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102905) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 55), (2, 61), (3, 3), (4, 71), (5, 69), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eb0) f9 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l1028e4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1028e4 :=
  Rest.liftedBlock (rest_l1028e4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1028e4 x hx)

theorem rest_l10290b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10290b bytes_l10290b) (entryMap (live .l10290b))
      6 0x10290b bytes_l10290b b_l10290b := by
  have f0 : InstrSpec 0x10290b [0x48, 0x8D, 0x9C, 0x24, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10290b) (leaR64Effect 0x10290b 3 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x10290b 3 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (lea_r64_effect_step 0x10290b 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102913 [0x4C, 0x8D, 0x25, 0xE6, 0x15, 0x00, 0x00] (fun s => s.RIP = 0x102913) (leaR64Effect 0x102913 12 (.rip 0x15e6))
      [] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x102913 12 (.rip 0x15e6)).toInstrSpec (lea_r64_effect_step 0x102913 0x4c (by decide) 4 (.rip 0x15e6) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10291a [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x10291a) (movR64R64Effect 0x10291a 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10291a 7 3).toInstrSpec (mov_r64_r64_effect_step 0x10291a 0x48 0xdf (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10291d [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x10291d) (movR64R64Effect 0x10291d 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10291d 6 13).toInstrSpec (mov_r64_r64_effect_step 0x10291d 0x4c 0xee (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x102920 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x102920) (movR64R64Effect 0x102920 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x102920 2 14).toInstrSpec (mov_r64_r64_effect_step 0x102920 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x102923 [0x41, 0xFF, 0xD4] (GoesTo (CallPre 0x102923 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x102926) 0x103f00) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x102926)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x102923 12 0x102926).toInstrSpec (call_r64_rex_effect_step 0x102923 0x41 0xd4 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 12 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (9, 9), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102913) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10291a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 53), (4, 4), (5, 5), (7, 57), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10291d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102920) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 61), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102923) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 61), (3, 53), (4, 63), (5, 5), (6, 59), (7, 57), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f5 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l10290b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10290b :=
  Rest.liftedBlock (rest_l10290b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10290b x hx)

theorem rest_l102926 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102926 bytes_l102926) (entryMap (live .l102926))
      7 0x102926 bytes_l102926 b_l102926 := by
  have f0 : InstrSpec 0x102926 [0x4C, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x102926 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102926 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102926 15 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102926 15 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x102926 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10292b [0x48, 0x89, 0x5C, 0x24, 0x18] (StorePre 0x10292b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10292b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10292b 3 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10292b 3 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10292b 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x102930 [0x48, 0x89, 0x5C, 0x24, 0x20] (StorePre 0x102930 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x102930 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102930 3 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102930 3 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x102930 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x102935 [0x48, 0xC7, 0x44, 0x24, 0x28, 0x01, 0x00, 0x00, 0x00] (StorePre 0x102935 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x102935 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102935 (.sib 4 none 0 (.d8 0x28)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102935 (.sib 4 none 0 (.d8 0x28)) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x102935 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10293e [0x48, 0x8D, 0x7C, 0x24, 0x58] (fun s => s.RIP = 0x10293e) (leaR64Effect 0x10293e 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10293e 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (lea_r64_effect_step 0x10293e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x102943 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x102943) (leaR64Effect 0x102943 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102943 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x102943 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x102948 [0xE8, 0x93, 0x5B, 0x00, 0x00] (PushPre 0x102948 5) (callEffect (fun _ => 0x1084e0) 0x10294d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102948 0x1084e0 0x10294d).toInstrSpec (call_rel32_effect_step 0x102948 0x5b93 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10292b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102930) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102935) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10293e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (7, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102943) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102948) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084e0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l102926 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102926 :=
  Rest.liftedBlock (rest_l102926 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102926 x hx)

theorem rest_l10294d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10294d bytes_l10294d) (entryMap (live .l10294d))
      5 0x10294d bytes_l10294d b_l10294d := by
  have f0 : InstrSpec 0x10294d [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x10294d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10294d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10294d 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10294d 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10294d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x102952 [0x48, 0x8B, 0x78, 0x08] (LoadPre 0x102952 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x102952 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102952 7 (.base 0 (.d8 0x8)))
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x102952 7 (.base 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x102952 0x48 (by decide) 7 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x102956 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x102956) (movR64R64Effect 0x102956 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102956 6 3).toInstrSpec (mov_r64_r64_effect_step 0x102956 0x48 0xde (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102959 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x102959) (movR64R64Effect 0x102959 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x102959 2 14).toInstrSpec (mov_r64_r64_effect_step 0x102959 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10295c [0x41, 0xFF, 0xD4] (GoesTo (CallPre 0x10295c 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10295f) 0x103f00) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10295f)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x10295c 12 0x10295f).toInstrSpec (call_r64_rex_effect_step 0x10295c 0x41 0xd4 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 12 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102952) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102956) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102959) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10295c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10294d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10294d :=
  Rest.liftedBlock (rest_l10294d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10294d x hx)

theorem rest_l10295f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10295f bytes_l10295f) (entryMap (live .l10295f))
      1 0x10295f bytes_l10295f b_l10295f := by
  have f0 : InstrSpec 0x10295f [0x89, 0xE8] (fun s => s.RIP = 0x10295f) (movR32R32Effect 0x10295f 2 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x10295f 2 0 5).toInstrSpec (mov_r32_r32_effect_step 0x10295f 0xe8 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102961) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l10295f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10295f :=
  Rest.liftedBlock (rest_l10295f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10295f x hx)

theorem rest_l102961 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102961 bytes_l102961) (entryMap (live .l102961))
      8 0x102961 bytes_l102961 b_l102961 := by
  have f0 : InstrSpec 0x102961 [0x48, 0x81, 0xC4, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102961) (addR64Imm32Effect 0x102961 4 0xa8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x102961 4 0xa8).toInstrSpec (add_r64_imm32_effect_step 0x102961 0x48 0xc4 0xa8 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102968 [0x5B] (PopPre 0x102968) (popR64Effect 0x102968 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102968 1 3).toInstrSpec (pop_r64_effect_step 0x102968 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x102969 [0x41, 0x5C] (PopPre 0x102969) (popR64Effect 0x102969 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102969 2 12).toInstrSpec (pop_r64_rex_effect_step 0x102969 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10296b [0x41, 0x5D] (PopPre 0x10296b) (popR64Effect 0x10296b 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10296b 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10296b 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10296d [0x41, 0x5E] (PopPre 0x10296d) (popR64Effect 0x10296d 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10296d 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10296d 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10296f [0x41, 0x5F] (PopPre 0x10296f) (popR64Effect 0x10296f 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10296f 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10296f 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x102971 [0x5D] (PopPre 0x102971) (popR64Effect 0x102971 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102971 1 5).toInstrSpec (pop_r64_effect_step 0x102971 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x102972 [0xC3] (RetPre 0x102972) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x102972).toInstrSpec (ret_effect_step 0x102972) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102968) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102969) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10296b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10296d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10296f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102971) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102972) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l102961 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102961 :=
  Rest.liftedBlock (rest_l102961 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102961 x hx)

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

theorem_by block_l102720_eval :
    program.runBlock (dialect code) ⟨.l102720, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102759_eval :
    program.runBlock (dialect code) ⟨.l102759, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1027bc_eval :
    program.runBlock (dialect code) ⟨.l1027bc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1027e8_eval :
    program.runBlock (dialect code) ⟨.l1027e8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102849_eval :
    program.runBlock (dialect code) ⟨.l102849, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102885_eval :
    program.runBlock (dialect code) ⟨.l102885, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1028d0_eval :
    program.runBlock (dialect code) ⟨.l1028d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1028d7_eval :
    program.runBlock (dialect code) ⟨.l1028d7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1028dc_eval :
    program.runBlock (dialect code) ⟨.l1028dc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1028e4_eval :
    program.runBlock (dialect code) ⟨.l1028e4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10290b_eval :
    program.runBlock (dialect code) ⟨.l10290b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102926_eval :
    program.runBlock (dialect code) ⟨.l102926, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10294d_eval :
    program.runBlock (dialect code) ⟨.l10294d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10295f_eval :
    program.runBlock (dialect code) ⟨.l10295f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102961_eval :
    program.runBlock (dialect code) ⟨.l102961, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
