import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l1022c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1022c0 bytes_l1022c0) (entryMap (live .l1022c0))
      17 0x1022c0 bytes_l1022c0 b_l1022c0 := by
  have f0 : InstrSpec 0x1022c0 [0x55] (PushPre 0x1022c0 1) (pushR64Effect 0x1022c0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1022c0 1 5).toInstrSpec (push_r64_effect_step 0x1022c0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1022c1 [0x41, 0x57] (PushPre 0x1022c1 2) (pushR64Effect 0x1022c1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1022c1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1022c1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1022c3 [0x41, 0x56] (PushPre 0x1022c3 2) (pushR64Effect 0x1022c3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1022c3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1022c3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1022c5 [0x41, 0x55] (PushPre 0x1022c5 2) (pushR64Effect 0x1022c5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1022c5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1022c5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1022c7 [0x41, 0x54] (PushPre 0x1022c7 2) (pushR64Effect 0x1022c7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1022c7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1022c7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1022c9 [0x53] (PushPre 0x1022c9 1) (pushR64Effect 0x1022c9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1022c9 1 3).toInstrSpec (push_r64_effect_step 0x1022c9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1022ca [0x48, 0x81, 0xEC, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1022ca) (subR64Imm32Effect 0x1022ca 4 0xa8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x1022ca 4 0xa8).toInstrSpec (sub_r64_imm32_effect_step 0x1022ca 0x48 0xec 0xa8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1022d1 [0x48, 0x89, 0xCD] (fun s => s.RIP = 0x1022d1) (movR64R64Effect 0x1022d1 5 1)
      [.gpr 1] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x1022d1 5 1).toInstrSpec (mov_r64_r64_effect_step 0x1022d1 0x48 0xcd (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1022d4 [0x48, 0xBB, 0xE0, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1022d4) (movR64Imm64Effect 0x1022d4 3 0xfffffffe0)
      [] [] [.reg 3, .rip] :=
    (movR64Imm64Effect_footprint 0x1022d4 3 0xfffffffe0).toInstrSpec (mov_r64_imm64_effect_step 0x1022d4 0x48 0xbb (by decide) (by decide) 0xfffffffe0) pre_rip
  have f9 : InstrSpec 0x1022de [0x4D, 0x8B, 0x70, 0x10] (LoadPre 0x1022de (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x1022de + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1022de 14 (.base 8 (.d8 0x10)))
      [.gpr 8] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x1022de 14 (.base 8 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1022de 0x4d (by decide) 6 (.base 8 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1022e2 [0x49, 0x39, 0xDE] (fun s => s.RIP = 0x1022e2) (cmpR64R64Effect 0x1022e2 14 3)
      [.gpr 14, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1022e2 14 3).toInstrSpec (cmp_r64_r64_effect_step 0x1022e2 0x49 0xde (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1022e5 [0x0F, 0x97, 0xC0] (fun s => s.RIP = 0x1022e5) (atFlags (condHolds 7) (setccR8Effect 0x1022e5 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x1022e5 3 0 7).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1022e5 7 0xc0 (by decide) (by decide) c)) pre_rip
  have f12 : InstrSpec 0x1022e8 [0x48, 0xC1, 0xE9, 0x3D] (fun s => s.RIP = 0x1022e8) (shrR64Effect 0x1022e8 4 1 61)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x1022e8 4 1 61).toInstrSpec (shr_r64_imm8_effect_step 0x1022e8 0x48 0xe9 0x3d (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1022ec [0x0F, 0x95, 0xC1] (fun s => s.RIP = 0x1022ec) (atFlags (condHolds 5) (setccR8Effect 0x1022ec 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x1022ec 3 1 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1022ec 5 0xc1 (by decide) (by decide) c)) pre_rip
  have f14 : InstrSpec 0x1022ef [0x08, 0xC1] (fun s => s.RIP = 0x1022ef) (orR8R8Effect 0x1022ef 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR8R8Effect_footprint 0x1022ef 2 1 0).toInstrSpec (or_r8_r8_effect_step 0x1022ef 0xc1 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1022f1 [0xB0, 0x01] (fun s => s.RIP = 0x1022f1) (movR8Imm8Effect 0x1022f1 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x1022f1 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x1022f1 0xb0 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022c3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022c5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022c7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022c9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022ca) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022d1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022d4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022de) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022e2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (16, 73), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022e5) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 1), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (16, 73), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022e8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 79) f12 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x1022e8 4 1 61 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 80) (ρ' := [(0, 76), (1, 78), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (19, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022ec) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 76), (1, 81), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (19, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022ef) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 84) f14 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 85) (ρ' := [(0, 76), (1, 83), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (19, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022f1) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 86), (1, 83), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (19, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022f3) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 88) (jcc_rel32_effect_step 0x1022f3 5 0x208) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1022c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1022c0 :=
  Rest.liftedBlock (rest_l1022c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1022c0 x hx)

theorem rest_l1022f9_1 [Bindings] (code : CodeMap) :
    Rest (n := 82) code lifted (codeRange 0x1022f9 bytes_l1022f9) [(0, 57), (1, 59), (2, 77), (3, 3), (4, 4), (5, 5), (6, 66), (7, 75), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x102357 bytes_l1022f9_1 b_l1022f9_1 := by
  have f20 : InstrSpec 0x102357 [0xE8, 0xA4, 0x2D, 0x00, 0x00] (PushPre 0x102357 5) (callEffect (fun _ => 0x105100) 0x10235c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102357 0x105100 0x10235c).toInstrSpec (call_rel32_effect_step 0x102357 0x2da4 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 57), (1, 59), (2, 77), (3, 3), (4, 82), (5, 5), (6, 66), (7, 75), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105100) f20 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 84) (by decide) (by decide) rfl rfl

theorem rest_l1022f9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1022f9 bytes_l1022f9) (entryMap (live .l1022f9))
      21 0x1022f9 bytes_l1022f9 b_l1022f9 := by
  have f0 : InstrSpec 0x1022f9 [0x4D, 0x89, 0xCD] (fun s => s.RIP = 0x1022f9) (movR64R64Effect 0x1022f9 13 9)
      [.gpr 9] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1022f9 13 9).toInstrSpec (mov_r64_r64_effect_step 0x1022f9 0x4d 0xcd (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1022fc [0x49, 0x89, 0xFC] (fun s => s.RIP = 0x1022fc) (movR64R64Effect 0x1022fc 12 7)
      [.gpr 7] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x1022fc 12 7).toInstrSpec (mov_r64_r64_effect_step 0x1022fc 0x49 0xfc (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1022ff [0x8B, 0x06] (LoadPre 0x1022ff (fun s => AddrMode.addr (.base 6 .none) s (0x1022ff + BitVec.ofNat 64 2)) 4) (movR32M32LowEffect 0x1022ff 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1022ff 0 (.base 6 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x1022ff 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x102301 [0x8B, 0x4E, 0x04] (LoadPre 0x102301 (fun s => AddrMode.addr (.base 6 (.d8 0x4)) s (0x102301 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x102301 1 (.base 6 (.d8 0x4)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x102301 1 (.base 6 (.d8 0x4))).toInstrSpec (mov_r32_m32_low_effect_step 0x102301 1 (.base 6 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x102304 [0x48, 0x89, 0x54, 0x24, 0x50] (StorePre 0x102304 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x102304 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102304 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102304 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x102304 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x102309 [0x8B, 0x56, 0x08] (LoadPre 0x102309 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x102309 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x102309 2 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x102309 2 (.base 6 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x102309 2 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10230c [0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10230c 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10230c + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10230c (.sib 4 none 0 (.d32 0x80)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10230c (.sib 4 none 0 (.d32 0x80)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10230c 0x48 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x102318 [0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102318 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x102318 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102318 (.sib 4 none 0 (.d8 0x78)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102318 (.sib 4 none 0 (.d8 0x78)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102318 0x48 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x102321 [0x48, 0x8D, 0x77, 0x20] (fun s => s.RIP = 0x102321) (leaR64Effect 0x102321 6 (.base 7 (.d8 0x20)))
      [.gpr 7] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102321 6 (.base 7 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x102321 0x48 (by decide) 6 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x102325 [0x89, 0x44, 0x24, 0x3C] (StorePre 0x102325 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x102325 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102325 0 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x102325 0 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_m32_r32_low_effect_step 0x102325 0 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x102329 [0x89, 0x44, 0x24, 0x10] (StorePre 0x102329 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102329 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102329 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x102329 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m32_r32_low_effect_step 0x102329 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x10232d [0x89, 0x4C, 0x24, 0x38] (StorePre 0x10232d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10232d + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10232d 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10232d 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m32_r32_low_effect_step 0x10232d 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x102331 [0x89, 0x4C, 0x24, 0x14] (StorePre 0x102331 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x102331 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102331 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x102331 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m32_r32_low_effect_step 0x102331 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x102335 [0x89, 0x54, 0x24, 0x34] (StorePre 0x102335 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x102335 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102335 2 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x102335 2 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x102335 2 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x102339 [0x89, 0x54, 0x24, 0x18] (StorePre 0x102339 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102339 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102339 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x102339 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m32_r32_low_effect_step 0x102339 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x10233d [0xC7, 0x44, 0x24, 0x1C, 0x00, 0x00, 0x00, 0x01] (StorePre 0x10233d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10233d + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x10233d 8 (.sib 4 none 0 (.d8 0x1c)) 0x1000000)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x10233d 8 (.sib 4 none 0 (.d8 0x1c)) 0x1000000).toInstrSpec (mov_m32_imm32_effect_step 0x10233d (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide) 0x1000000) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x102345 [0x48, 0x8D, 0x7C, 0x24, 0x78] (fun s => s.RIP = 0x102345) (leaR64Effect 0x102345 7 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102345 7 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x102345 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10234a [0x48, 0x8D, 0x54, 0x24, 0x10] (fun s => s.RIP = 0x10234a) (leaR64Effect 0x10234a 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x10234a 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x10234a 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10234f [0x48, 0x89, 0x74, 0x24, 0x48] (StorePre 0x10234f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10234f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10234f 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10234f 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x10234f 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x102354 [0x4D, 0x89, 0xC7] (fun s => s.RIP = 0x102354) (movR64R64Effect 0x102354 15 8)
      [.gpr 8] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x102354 15 8).toInstrSpec (mov_r64_r64_effect_step 0x102354 0x4d 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022fc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022ff) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102301) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102304) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102309) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10230c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102318) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102321) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102325) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102329) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10232d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102331) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102335) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102339) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10233d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102345) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 57), (1, 59), (2, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 75), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10234a) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 57), (1, 59), (2, 77), (3, 3), (4, 4), (5, 5), (6, 66), (7, 75), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10234f) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 57), (1, 59), (2, 77), (3, 3), (4, 4), (5, 5), (6, 66), (7, 75), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102354) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f19 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 57), (1, 59), (2, 77), (3, 3), (4, 4), (5, 5), (6, 66), (7, 75), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102357) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1022f9_1 code

theorem block_l1022f9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1022f9 :=
  Rest.liftedBlock (rest_l1022f9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1022f9 x hx)

theorem rest_l10235c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10235c bytes_l10235c) (entryMap (live .l10235c))
      10 0x10235c bytes_l10235c b_l10235c := by
  have f0 : InstrSpec 0x10235c [0x4C, 0x89, 0x7C, 0x24, 0x40] (StorePre 0x10235c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10235c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10235c 15 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10235c 15 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x10235c 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x102361 [0x4D, 0x8B, 0x0F] (LoadPre 0x102361 (fun s => AddrMode.addr (.base 15 .none) s (0x102361 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x102361 9 (.base 15 .none))
      [.gpr 15] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x102361 9 (.base 15 .none)).toInstrSpec (mov_r64_m64_effect_step 0x102361 0x4d (by decide) 1 (.base 15 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x102364 [0x4C, 0x89, 0x34, 0x24] (StorePre 0x102364 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102364 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102364 14 (.sib 4 none 0 .none))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102364 14 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x102364 0x4c (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x102368 [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102368) (leaR64Effect 0x102368 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102368 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x102368 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x102370 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x102370) (movR64R64Effect 0x102370 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102370 6 12).toInstrSpec (mov_r64_r64_effect_step 0x102370 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x102373 [0x48, 0x8D, 0x54, 0x24, 0x78] (fun s => s.RIP = 0x102373) (leaR64Effect 0x102373 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x102373 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x102373 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x102378 [0x48, 0x8B, 0x4C, 0x24, 0x50] (LoadPre 0x102378 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x102378 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102378 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x102378 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x102378 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10237d [0x49, 0x89, 0xE8] (fun s => s.RIP = 0x10237d) (movR64R64Effect 0x10237d 8 5)
      [.gpr 5] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10237d 8 5).toInstrSpec (mov_r64_r64_effect_step 0x10237d 0x49 0xe8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x102380 [0x4D, 0x89, 0xCC] (fun s => s.RIP = 0x102380) (movR64R64Effect 0x102380 12 9)
      [.gpr 9] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x102380 12 9).toInstrSpec (mov_r64_r64_effect_step 0x102380 0x4d 0xcc (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x102383 [0xE8, 0x78, 0xF4, 0xFF, 0xFF] (PushPre 0x102383 5) (callEffect (fun _ => 0x101800) 0x102388)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102383 0x101800 0x102388).toInstrSpec (call_rel32_effect_step 0x102383 0xfffff478 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102361) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 54), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102364) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 54), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102368) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 57), (9, 54), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102370) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 54), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102373) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 54), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102378) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 63), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 54), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10237d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 63), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (8, 65), (9, 54), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102380) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 63), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (8, 65), (9, 54), (11, 11), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102383) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 63), (2, 61), (3, 3), (4, 69), (5, 5), (6, 59), (7, 57), (8, 65), (9, 54), (11, 11), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101800) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l10235c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10235c :=
  Rest.liftedBlock (rest_l10235c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10235c x hx)

theorem rest_l102388_1 [Bindings] (code : CodeMap) :
    Rest (n := 95) code lifted (codeRange 0x102388 bytes_l102388) [(0, 92), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x1023d6 bytes_l102388_1 b_l102388_1 := by
  have f20 : InstrSpec 0x1023d6 [0x48, 0x8D, 0x44, 0x24, 0x10] (fun s => s.RIP = 0x1023d6) (leaR64Effect 0x1023d6 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1023d6 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1023d6 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x1023db [0x80, 0x7C, 0x24, 0x10, 0x00] (LoadPre 0x1023db (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1023db + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x1023db 5 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x1023db 5 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x1023db (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x1023e0 [0x0F, 0x94, 0xC0] (fun s => s.RIP = 0x1023e0) (atFlags (condHolds 4) (setccR8Effect 0x1023e0 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x1023e0 3 0 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1023e0 4 0xc0 (by decide) (by decide) c)) pre_rip
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023db) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f21 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 95), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023e0) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 99), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023e3) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 101) (jcc_rel32_effect_step 0x1023e3 4 0x118) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l102388 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102388 bytes_l102388) (entryMap (live .l102388))
      24 0x102388 bytes_l102388 b_l102388 := by
  have f0 : InstrSpec 0x102388 [0x48, 0x8B, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x102388 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x102388 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102388 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x102388 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x102388 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x102390 [0x48, 0x8B, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x102390 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x102390 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102390 6 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x102390 6 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x102390 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x102398 [0x49, 0x8B, 0x7D, 0x00] (LoadPre 0x102398 (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x102398 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102398 7 (.base 13 (.d8 0x0)))
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x102398 7 (.base 13 (.d8 0x0))).toInstrSpec (mov_r64_m64_effect_step 0x102398 0x49 (by decide) 7 (.base 13 (.d8 0x0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10239c [0x4D, 0x8B, 0x45, 0x08] (LoadPre 0x10239c (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x10239c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10239c 8 (.base 13 (.d8 0x8)))
      [.gpr 13] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10239c 8 (.base 13 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10239c 0x4d (by decide) 0 (.base 13 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1023a0 [0x31, 0xC0] (fun s => s.RIP = 0x1023a0) (xorR32R32Effect 0x1023a0 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1023a0 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x1023a0 0xc0 (by decide)) pre_rip
  have f5 : InstrSpec 0x1023a2 [0x66, 0xB9, 0x01, 0x00] (fun s => s.RIP = 0x1023a2) (movR16Imm16Effect 0x1023a2 4 1 0x1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR16Imm16Effect_footprint 0x1023a2 4 1 0x1).toInstrSpec (mov_r16_imm16_effect_step 0x1023a2 0xb9 (by decide) 0x1) pre_rip
  have f6 : InstrSpec 0x1023a6 [0x66, 0x41, 0xB9, 0x01, 0x00] (fun s => s.RIP = 0x1023a6) (movR16Imm16Effect 0x1023a6 5 9 0x1)
      [.gpr 9] [] [.reg 9, .rip] :=
    (movR16Imm16Effect_footprint 0x1023a6 5 9 0x1).toInstrSpec (mov_r16_imm16_rex_effect_step 0x1023a6 0x41 (by decide) 0xb9 (by decide) 0x1) pre_rip
  have f7 : InstrSpec 0x1023ab [0x48, 0x31, 0xFA] (fun s => s.RIP = 0x1023ab) (xorR64R64Effect 0x1023ab 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1023ab 2 7).toInstrSpec (xor_r64_r64_effect_step 0x1023ab 0x48 0xfa (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1023ae [0x4C, 0x0F, 0x45, 0xC8] (fun s => s.RIP = 0x1023ae) (atFlags (condHolds 5) (cmovR64R64Effect 0x1023ae 4 9 0))
      [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 9, .rip] :=
    (cmovR64R64Effect_footprint 0x1023ae 4 9 0 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x1023ae 5 0x4c (by decide) 0xc8 (by decide) c)) pre_rip
  have f9 : InstrSpec 0x1023b2 [0x41, 0x0F, 0xB6, 0xD1] (fun s => s.RIP = 0x1023b2) (movzxR32R8Effect 0x1023b2 4 2 9)
      [.gpr 9] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x1023b2 4 2 9).toInstrSpec (movzx_r32_r8_rex_effect_step 0x1023b2 0x41 (by decide) 0xd1 (by decide)) pre_rip
  have f10 : InstrSpec 0x1023b6 [0x4C, 0x31, 0xC6] (fun s => s.RIP = 0x1023b6) (xorR64R64Effect 0x1023b6 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1023b6 6 8).toInstrSpec (xor_r64_r64_effect_step 0x1023b6 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1023b9 [0x48, 0x0F, 0x45, 0xD0] (fun s => s.RIP = 0x1023b9) (atFlags (condHolds 5) (cmovR64R64Effect 0x1023b9 4 2 0))
      [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x1023b9 4 2 0 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x1023b9 5 0x48 (by decide) 0xd0 (by decide) c)) pre_rip
  have f12 : InstrSpec 0x1023bd [0x0F, 0xB6, 0xD2] (fun s => s.RIP = 0x1023bd) (movzxR32R8Effect 0x1023bd 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x1023bd 3 2 2).toInstrSpec (movzx_r32_r8_effect_step 0x1023bd 0xd2 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1023c0 [0x31, 0xF6] (fun s => s.RIP = 0x1023c0) (xorR32R32Effect 0x1023c0 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1023c0 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x1023c0 0xf6 (by decide)) pre_rip
  have f14 : InstrSpec 0x1023c2 [0x48, 0x31, 0xC6] (fun s => s.RIP = 0x1023c2) (xorR64R64Effect 0x1023c2 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1023c2 6 0).toInstrSpec (xor_r64_r64_effect_step 0x1023c2 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1023c5 [0x48, 0x0F, 0x45, 0xD0] (fun s => s.RIP = 0x1023c5) (atFlags (condHolds 5) (cmovR64R64Effect 0x1023c5 4 2 0))
      [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x1023c5 4 2 0 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x1023c5 5 0x48 (by decide) 0xd0 (by decide) c)) pre_rip
  have f16 : InstrSpec 0x1023c9 [0x0F, 0xB6, 0xD2] (fun s => s.RIP = 0x1023c9) (movzxR32R8Effect 0x1023c9 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x1023c9 3 2 2).toInstrSpec (movzx_r32_r8_effect_step 0x1023c9 0xd2 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1023cc [0x66, 0x31, 0xCA] (fun s => s.RIP = 0x1023cc) (xorR16R16Effect 0x1023cc 3 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR16R16Effect_footprint 0x1023cc 3 2 1).toInstrSpec (xor_r16_r16_effect_step 0x1023cc 0xca (by decide)) pre_rip
  have f18 : InstrSpec 0x1023cf [0x0F, 0x44, 0xC1] (fun s => s.RIP = 0x1023cf) (atFlags (condHolds 4) (cmovR32R32Effect 0x1023cf 3 0 1))
      [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (cmovR32R32Effect_footprint 0x1023cf 3 0 1 4).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_effect_step 0x1023cf 4 0xc1 (by decide) c)) pre_rip
  have f19 : InstrSpec 0x1023d2 [0x88, 0x44, 0x24, 0x10] (StorePre 0x1023d2 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1023d2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1023d2 4 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1023d2 4 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x1023d2 0 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102390) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102398) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10239c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023a0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023a2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023a6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 63), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 65), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023ab) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 65), (11, 11), (12, 12), (13, 13), (14, 14), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023ae) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023b2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 61), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023b6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 61), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 73), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023b9) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 61), (1, 63), (2, 76), (3, 3), (4, 4), (5, 5), (6, 73), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023bd) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 61), (1, 63), (2, 78), (3, 3), (4, 4), (5, 5), (6, 73), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023c0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 61), (1, 63), (2, 78), (3, 3), (4, 4), (5, 5), (6, 80), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023c2) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f14 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 61), (1, 63), (2, 78), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023c5) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 61), (1, 63), (2, 85), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023c9) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 61), (1, 63), (2, 87), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023cc) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 90) f17 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 91) (ρ' := [(0, 61), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023cf) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 92), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023d2) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 92), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023d6) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l102388_1 code

theorem block_l102388 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102388 :=
  Rest.liftedBlock (rest_l102388 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102388 x hx)

theorem rest_l1023e9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1023e9 bytes_l1023e9) (entryMap (live .l1023e9))
      13 0x1023e9 bytes_l1023e9 b_l1023e9 := by
  have f0 : InstrSpec 0x1023e9 [0x48, 0x8B, 0x4C, 0x24, 0x48] (LoadPre 0x1023e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1023e9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1023e9 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1023e9 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x1023e9 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1023ee [0x48, 0x89, 0x4C, 0x24, 0x58] (StorePre 0x1023ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1023ee + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1023ee 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1023ee 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x1023ee 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1023f3 [0x4C, 0x8D, 0x7C, 0x24, 0x60] (fun s => s.RIP = 0x1023f3) (leaR64Effect 0x1023f3 15 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x1023f3 15 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (lea_r64_effect_step 0x1023f3 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1023f8 [0x8B, 0x4C, 0x24, 0x3C] (LoadPre 0x1023f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x1023f8 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1023f8 1 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x1023f8 1 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r32_m32_low_effect_step 0x1023f8 1 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1023fc [0x89, 0x4C, 0x24, 0x60] (StorePre 0x1023fc 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1023fc + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1023fc 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1023fc 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m32_r32_low_effect_step 0x1023fc 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x102400 [0x8B, 0x4C, 0x24, 0x38] (LoadPre 0x102400 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x102400 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x102400 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x102400 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r32_m32_low_effect_step 0x102400 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x102404 [0x89, 0x4C, 0x24, 0x64] (StorePre 0x102404 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x102404 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102404 1 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x102404 1 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (mov_m32_r32_low_effect_step 0x102404 1 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x102408 [0x8B, 0x4C, 0x24, 0x34] (LoadPre 0x102408 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x102408 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x102408 1 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x102408 1 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r32_m32_low_effect_step 0x102408 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10240c [0x89, 0x4C, 0x24, 0x68] (StorePre 0x10240c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10240c + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10240c 1 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10240c 1 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m32_r32_low_effect_step 0x10240c 1 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x102410 [0x48, 0xB9, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102410) (movR64Imm64Effect 0x102410 1 0x100000001)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x102410 1 0x100000001).toInstrSpec (mov_r64_imm64_effect_step 0x102410 0x48 0xb9 (by decide) (by decide) 0x100000001) pre_rip
  have f10 : InstrSpec 0x10241a [0x48, 0x89, 0x4C, 0x24, 0x6C] (StorePre 0x10241a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x10241a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10241a 1 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10241a 1 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (mov_m64_r64_effect_step 0x10241a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x10241f [0x49, 0x83, 0xFE, 0x11] (fun s => s.RIP = 0x10241f) (cmpR64Imm8Effect 0x10241f 14 0x11)
      [.gpr 14] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x10241f 14 0x11).toInstrSpec (cmp_r64_imm8_effect_step 0x10241f 0x49 0xfe 0x11 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023ee) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023f3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023f8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 58), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1023fc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 58), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102400) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102404) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102408) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10240c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102410) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10241a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10241f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (16, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102423) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 72) (jcc_rel8_effect_step 0x102423 2 0x57) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1023e9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1023e9 :=
  Rest.liftedBlock (rest_l1023e9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1023e9 x hx)

theorem rest_l102425 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102425 bytes_l102425) (entryMap (live .l102425))
      18 0x102425 bytes_l102425 b_l102425 := by
  have f0 : InstrSpec 0x102425 [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x102425) (movR64R64Effect 0x102425 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102425 1 14).toInstrSpec (mov_r64_r64_effect_step 0x102425 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102428 [0x48, 0xC1, 0xE9, 0x04] (fun s => s.RIP = 0x102428) (shrR64Effect 0x102428 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x102428 4 1 4).toInstrSpec (shr_r64_imm8_effect_step 0x102428 0x48 0xe9 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10242c [0x48, 0x8B, 0x74, 0x24, 0x40] (LoadPre 0x10242c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10242c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10242c 6 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10242c 6 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10242c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x102431 [0x48, 0x8B, 0x56, 0x08] (LoadPre 0x102431 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x102431 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102431 2 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x102431 2 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x102431 0x48 (by decide) 2 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x102435 [0x48, 0x83, 0xC3, 0x10] (fun s => s.RIP = 0x102435) (addR64Imm8Effect 0x102435 3 0x10)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x102435 3 0x10).toInstrSpec (add_r64_imm8_effect_step 0x102435 0x48 0xc3 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x102439 [0x4C, 0x21, 0xF3] (fun s => s.RIP = 0x102439) (andR64R64Effect 0x102439 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102439 3 14).toInstrSpec (and_r64_r64_effect_step 0x102439 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10243c [0x41, 0x83, 0xE6, 0x0F] (fun s => s.RIP = 0x10243c) (andR32Imm8Effect 0x10243c 4 14 0xf)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x10243c 4 14 0xf).toInstrSpec (and_r32_imm8_rex_effect_step 0x10243c 0x41 0xe6 0xf (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x102440 [0x4D, 0x8D, 0x2C, 0x1C] (fun s => s.RIP = 0x102440) (leaR64Effect 0x102440 13 (.sib 12 (some 3) 0 .none))
      [.gpr 12, .gpr 3] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x102440 13 (.sib 12 (some 3) 0 .none)).toInstrSpec (lea_r64_effect_step 0x102440 0x4d (by decide) 5 (.sib 12 (some 3) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x102444 [0x48, 0x01, 0xD3] (fun s => s.RIP = 0x102444) (addR64R64Effect 0x102444 3 2)
      [.gpr 3, .gpr 2] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x102444 3 2).toInstrSpec (add_r64_r64_effect_step 0x102444 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x102447 [0x48, 0x89, 0x5E, 0x08] (StorePre 0x102447 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x102447 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102447 3 (.base 6 (.d8 0x8)))
      [.gpr 3, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x102447 3 (.base 6 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x102447 0x48 (by decide) 3 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10244b [0x4C, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x10244b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10244b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10244b 15 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10244b 15 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10244b 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x102450 [0x4C, 0x89, 0x64, 0x24, 0x18] (StorePre 0x102450 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102450 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102450 12 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102450 12 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x102450 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x102455 [0x48, 0x89, 0x54, 0x24, 0x20] (StorePre 0x102455 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x102455 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102455 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102455 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x102455 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x10245a [0x48, 0x89, 0x4C, 0x24, 0x28] (StorePre 0x10245a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10245a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10245a 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10245a 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10245a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x10245f [0x48, 0x8D, 0x7C, 0x24, 0x58] (fun s => s.RIP = 0x10245f) (leaR64Effect 0x10245f 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10245f 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (lea_r64_effect_step 0x10245f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x102464 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x102464) (leaR64Effect 0x102464 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102464 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x102464 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x102469 [0x89, 0xC3] (fun s => s.RIP = 0x102469) (movR32R32Effect 0x102469 2 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x102469 2 3 0).toInstrSpec (mov_r32_r32_effect_step 0x102469 0xc3 (by decide)) pre_rip
  have f17 : InstrSpec 0x10246b [0xE8, 0xE0, 0x4B, 0x00, 0x00] (PushPre 0x10246b 5) (callEffect (fun _ => 0x107050) 0x102470)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10246b 0x107050 0x102470).toInstrSpec (call_rel32_effect_step 0x10246b 0x4be0 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102428) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10242c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102431) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102435) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 61), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102439) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 63), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10243c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 63), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102440) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 63), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102444) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 69), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102447) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 69), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10244b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 69), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102450) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 69), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102455) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 69), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10245a) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 69), (4, 4), (5, 5), (6, 57), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10245f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 69), (4, 4), (5, 5), (6, 57), (7, 76), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102464) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 69), (4, 4), (5, 5), (6, 78), (7, 76), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102469) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 80), (4, 4), (5, 5), (6, 78), (7, 76), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10246b) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f17 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 80), (4, 82), (5, 5), (6, 78), (7, 76), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107050) f17 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 84) (by decide) (by decide) rfl rfl

theorem block_l102425 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102425 :=
  Rest.liftedBlock (rest_l102425 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102425 x hx)

theorem rest_l102470 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102470 bytes_l102470) (entryMap (live .l102470))
      3 0x102470 bytes_l102470 b_l102470 := by
  have f0 : InstrSpec 0x102470 [0x89, 0xD8] (fun s => s.RIP = 0x102470) (movR32R32Effect 0x102470 2 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x102470 2 0 3).toInstrSpec (mov_r32_r32_effect_step 0x102470 0xd8 (by decide)) pre_rip
  have f1 : InstrSpec 0x102472 [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x102472) (testR64R64Effect 0x102472 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x102472 14 14).toInstrSpec (test_r64_r64_effect_step 0x102472 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102472) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102475) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x102475 5 0xd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102470 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102470 :=
  Rest.liftedBlock (rest_l102470 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102470 x hx)

theorem rest_l102477 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102477 bytes_l102477) (entryMap (live .l102477))
      1 0x102477 bytes_l102477 b_l102477 := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x102477 0x85 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l102477 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102477 :=
  Rest.liftedBlock (rest_l102477 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102477 x hx)

theorem rest_l10247c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10247c bytes_l10247c) (entryMap (live .l10247c))
      3 0x10247c bytes_l10247c b_l10247c := by
  have f0 : InstrSpec 0x10247c [0x4D, 0x89, 0xE5] (fun s => s.RIP = 0x10247c) (movR64R64Effect 0x10247c 13 12)
      [.gpr 12] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10247c 13 12).toInstrSpec (mov_r64_r64_effect_step 0x10247c 0x4d 0xe5 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10247f [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x10247f) (testR64R64Effect 0x10247f 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x10247f 14 14).toInstrSpec (test_r64_r64_effect_step 0x10247f 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10247f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102482) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x102482 4 0x7d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10247c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10247c :=
  Rest.liftedBlock (rest_l10247c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10247c x hx)

theorem rest_l102484 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102484 bytes_l102484) (entryMap (live .l102484))
      10 0x102484 bytes_l102484 b_l102484 := by
  have f0 : InstrSpec 0x102484 [0xB9, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102484) (movR32Imm32Effect 0x102484 5 1 0x10)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x102484 5 1 0x10).toInstrSpec (mov_r32_imm32_effect_step 0x102484 0xb9 (by decide) 0x10) pre_rip
  have f1 : InstrSpec 0x102489 [0x4C, 0x29, 0xF1] (fun s => s.RIP = 0x102489) (subR64R64Effect 0x102489 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x102489 1 14).toInstrSpec (sub_r64_r64_effect_step 0x102489 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10248c [0x31, 0xD2] (fun s => s.RIP = 0x10248c) (xorR32R32Effect 0x10248c 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10248c 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x10248c 0xd2 (by decide)) pre_rip
  have f3 : InstrSpec 0x10248e [0x49, 0x83, 0xFE, 0x10] (fun s => s.RIP = 0x10248e) (cmpR64Imm8Effect 0x10248e 14 0x10)
      [.gpr 14] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x10248e 14 0x10).toInstrSpec (cmp_r64_imm8_effect_step 0x10248e 0x49 0xfe 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x102492 [0x48, 0x0F, 0x42, 0xD1] (fun s => s.RIP = 0x102492) (atFlags (condHolds 2) (cmovR64R64Effect 0x102492 4 2 1))
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x102492 4 2 1 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x102492 2 0x48 (by decide) 0xd1 (by decide) c)) pre_rip
  have f5 : InstrSpec 0x102496 [0x4A, 0x8D, 0x3C, 0x34] (fun s => s.RIP = 0x102496) (leaR64Effect 0x102496 7 (.sib 4 (some 14) 0 .none))
      [.gpr 4, .gpr 14] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102496 7 (.sib 4 (some 14) 0 .none)).toInstrSpec (lea_r64_effect_step 0x102496 0x4a (by decide) 7 (.sib 4 (some 14) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10249a [0x48, 0x81, 0xC7, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10249a) (addR64Imm32Effect 0x10249a 7 0x98)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x10249a 7 0x98).toInstrSpec (add_r64_imm32_effect_step 0x10249a 0x48 0xc7 0x98 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1024a1 [0x31, 0xF6] (fun s => s.RIP = 0x1024a1) (xorR32R32Effect 0x1024a1 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1024a1 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x1024a1 0xf6 (by decide)) pre_rip
  have f8 : InstrSpec 0x1024a3 [0x89, 0xC5] (fun s => s.RIP = 0x1024a3) (movR32R32Effect 0x1024a3 2 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x1024a3 2 5 0).toInstrSpec (mov_r32_r32_effect_step 0x1024a3 0xc5 (by decide)) pre_rip
  have f9 : InstrSpec 0x1024a5 [0xFF, 0x15, 0x7D, 0xED, 0x0F, 0x00] (GoesTo (CallMemPre 0x1024a5 (.rip 0xfed7d)) (callEffect (callMemPtr 0x1024a5 (.rip 0xfed7d)) (0x1024a5 + BitVec.ofNat 64 (callMemLen (.rip 0xfed7d)))) 0x103eb0) (callEffect (callMemPtr 0x1024a5 (.rip 0xfed7d)) (0x1024a5 + BitVec.ofNat 64 (callMemLen (.rip 0xfed7d))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1024a5 (.rip 0xfed7d)).toInstrSpec (call_m64_effect_step 0x1024a5 (.rip 0xfed7d) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103eb0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102489) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10248c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10248e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102492) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 61), (3, 3), (4, 4), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102496) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 61), (3, 3), (4, 4), (6, 6), (7, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10249a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 61), (3, 3), (4, 4), (6, 6), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024a1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 55), (2, 61), (3, 3), (4, 4), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024a3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 55), (2, 61), (3, 3), (4, 4), (5, 69), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024a5) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 55), (2, 61), (3, 3), (4, 71), (5, 69), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eb0) f9 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l102484 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102484 :=
  Rest.liftedBlock (rest_l102484 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102484 x hx)

theorem rest_l1024ab [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1024ab bytes_l1024ab) (entryMap (live .l1024ab))
      6 0x1024ab bytes_l1024ab b_l1024ab := by
  have f0 : InstrSpec 0x1024ab [0x48, 0x8D, 0x9C, 0x24, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1024ab) (leaR64Effect 0x1024ab 3 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x1024ab 3 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (lea_r64_effect_step 0x1024ab 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1024b3 [0x4C, 0x8D, 0x25, 0x46, 0x1A, 0x00, 0x00] (fun s => s.RIP = 0x1024b3) (leaR64Effect 0x1024b3 12 (.rip 0x1a46))
      [] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x1024b3 12 (.rip 0x1a46)).toInstrSpec (lea_r64_effect_step 0x1024b3 0x4c (by decide) 4 (.rip 0x1a46) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1024ba [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x1024ba) (movR64R64Effect 0x1024ba 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1024ba 7 3).toInstrSpec (mov_r64_r64_effect_step 0x1024ba 0x48 0xdf (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1024bd [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x1024bd) (movR64R64Effect 0x1024bd 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1024bd 6 13).toInstrSpec (mov_r64_r64_effect_step 0x1024bd 0x4c 0xee (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1024c0 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x1024c0) (movR64R64Effect 0x1024c0 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1024c0 2 14).toInstrSpec (mov_r64_r64_effect_step 0x1024c0 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1024c3 [0x41, 0xFF, 0xD4] (GoesTo (CallPre 0x1024c3 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x1024c6) 0x103f00) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x1024c6)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x1024c3 12 0x1024c6).toInstrSpec (call_r64_rex_effect_step 0x1024c3 0x41 0xd4 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 12 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (9, 9), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024b3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024ba) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 53), (4, 4), (5, 5), (7, 57), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024bd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024c0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 61), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024c3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 61), (3, 53), (4, 63), (5, 5), (6, 59), (7, 57), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f5 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l1024ab [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1024ab :=
  Rest.liftedBlock (rest_l1024ab code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1024ab x hx)

theorem rest_l1024c6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1024c6 bytes_l1024c6) (entryMap (live .l1024c6))
      7 0x1024c6 bytes_l1024c6 b_l1024c6 := by
  have f0 : InstrSpec 0x1024c6 [0x4C, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x1024c6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1024c6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1024c6 15 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1024c6 15 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1024c6 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1024cb [0x48, 0x89, 0x5C, 0x24, 0x18] (StorePre 0x1024cb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1024cb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1024cb 3 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1024cb 3 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1024cb 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1024d0 [0x48, 0x89, 0x5C, 0x24, 0x20] (StorePre 0x1024d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1024d0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1024d0 3 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1024d0 3 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1024d0 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1024d5 [0x48, 0xC7, 0x44, 0x24, 0x28, 0x01, 0x00, 0x00, 0x00] (StorePre 0x1024d5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1024d5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1024d5 (.sib 4 none 0 (.d8 0x28)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1024d5 (.sib 4 none 0 (.d8 0x28)) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x1024d5 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1024de [0x48, 0x8D, 0x7C, 0x24, 0x58] (fun s => s.RIP = 0x1024de) (leaR64Effect 0x1024de 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1024de 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (lea_r64_effect_step 0x1024de 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1024e3 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x1024e3) (leaR64Effect 0x1024e3 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1024e3 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1024e3 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1024e8 [0xE8, 0x63, 0x4B, 0x00, 0x00] (PushPre 0x1024e8 5) (callEffect (fun _ => 0x107050) 0x1024ed)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1024e8 0x107050 0x1024ed).toInstrSpec (call_rel32_effect_step 0x1024e8 0x4b63 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024cb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024d0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024d5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024de) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (7, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024e3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024e8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107050) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l1024c6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1024c6 :=
  Rest.liftedBlock (rest_l1024c6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1024c6 x hx)

theorem rest_l1024ed [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1024ed bytes_l1024ed) (entryMap (live .l1024ed))
      5 0x1024ed bytes_l1024ed b_l1024ed := by
  have f0 : InstrSpec 0x1024ed [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x1024ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1024ed + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1024ed 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1024ed 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1024ed 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1024f2 [0x48, 0x8B, 0x78, 0x08] (LoadPre 0x1024f2 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x1024f2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1024f2 7 (.base 0 (.d8 0x8)))
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1024f2 7 (.base 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1024f2 0x48 (by decide) 7 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1024f6 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x1024f6) (movR64R64Effect 0x1024f6 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1024f6 6 3).toInstrSpec (mov_r64_r64_effect_step 0x1024f6 0x48 0xde (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1024f9 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x1024f9) (movR64R64Effect 0x1024f9 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1024f9 2 14).toInstrSpec (mov_r64_r64_effect_step 0x1024f9 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1024fc [0x41, 0xFF, 0xD4] (GoesTo (CallPre 0x1024fc 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x1024ff) 0x103f00) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x1024ff)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x1024fc 12 0x1024ff).toInstrSpec (call_r64_rex_effect_step 0x1024fc 0x41 0xd4 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 12 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024f2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024f6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024f9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024fc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l1024ed [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1024ed :=
  Rest.liftedBlock (rest_l1024ed code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1024ed x hx)

theorem rest_l1024ff [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1024ff bytes_l1024ff) (entryMap (live .l1024ff))
      1 0x1024ff bytes_l1024ff b_l1024ff := by
  have f0 : InstrSpec 0x1024ff [0x89, 0xE8] (fun s => s.RIP = 0x1024ff) (movR32R32Effect 0x1024ff 2 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1024ff 2 0 5).toInstrSpec (mov_r32_r32_effect_step 0x1024ff 0xe8 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102501) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1024ff [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1024ff :=
  Rest.liftedBlock (rest_l1024ff code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1024ff x hx)

theorem rest_l102501 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102501 bytes_l102501) (entryMap (live .l102501))
      8 0x102501 bytes_l102501 b_l102501 := by
  have f0 : InstrSpec 0x102501 [0x48, 0x81, 0xC4, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102501) (addR64Imm32Effect 0x102501 4 0xa8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x102501 4 0xa8).toInstrSpec (add_r64_imm32_effect_step 0x102501 0x48 0xc4 0xa8 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102508 [0x5B] (PopPre 0x102508) (popR64Effect 0x102508 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102508 1 3).toInstrSpec (pop_r64_effect_step 0x102508 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x102509 [0x41, 0x5C] (PopPre 0x102509) (popR64Effect 0x102509 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102509 2 12).toInstrSpec (pop_r64_rex_effect_step 0x102509 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10250b [0x41, 0x5D] (PopPre 0x10250b) (popR64Effect 0x10250b 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10250b 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10250b 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10250d [0x41, 0x5E] (PopPre 0x10250d) (popR64Effect 0x10250d 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10250d 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10250d 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10250f [0x41, 0x5F] (PopPre 0x10250f) (popR64Effect 0x10250f 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10250f 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10250f 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x102511 [0x5D] (PopPre 0x102511) (popR64Effect 0x102511 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102511 1 5).toInstrSpec (pop_r64_effect_step 0x102511 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x102512 [0xC3] (RetPre 0x102512) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x102512).toInstrSpec (ret_effect_step 0x102512) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102508) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102509) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10250b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10250d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10250f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102511) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102512) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l102501 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102501 :=
  Rest.liftedBlock (rest_l102501 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102501 x hx)

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

theorem_by block_l1022c0_eval :
    program.runBlock (dialect code) ⟨.l1022c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1022f9_eval :
    program.runBlock (dialect code) ⟨.l1022f9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10235c_eval :
    program.runBlock (dialect code) ⟨.l10235c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102388_eval :
    program.runBlock (dialect code) ⟨.l102388, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1023e9_eval :
    program.runBlock (dialect code) ⟨.l1023e9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102425_eval :
    program.runBlock (dialect code) ⟨.l102425, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102470_eval :
    program.runBlock (dialect code) ⟨.l102470, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102477_eval :
    program.runBlock (dialect code) ⟨.l102477, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10247c_eval :
    program.runBlock (dialect code) ⟨.l10247c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102484_eval :
    program.runBlock (dialect code) ⟨.l102484, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1024ab_eval :
    program.runBlock (dialect code) ⟨.l1024ab, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1024c6_eval :
    program.runBlock (dialect code) ⟨.l1024c6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1024ed_eval :
    program.runBlock (dialect code) ⟨.l1024ed, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1024ff_eval :
    program.runBlock (dialect code) ⟨.l1024ff, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102501_eval :
    program.runBlock (dialect code) ⟨.l102501, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
