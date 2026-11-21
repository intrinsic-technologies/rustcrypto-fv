import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l102520 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102520 bytes_l102520) (entryMap (live .l102520))
      17 0x102520 bytes_l102520 b_l102520 := by
  have f0 : InstrSpec 0x102520 [0x55] (PushPre 0x102520 1) (pushR64Effect 0x102520 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102520 1 5).toInstrSpec (push_r64_effect_step 0x102520 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x102521 [0x41, 0x57] (PushPre 0x102521 2) (pushR64Effect 0x102521 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102521 2 15).toInstrSpec (push_r64_rex_effect_step 0x102521 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x102523 [0x41, 0x56] (PushPre 0x102523 2) (pushR64Effect 0x102523 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102523 2 14).toInstrSpec (push_r64_rex_effect_step 0x102523 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x102525 [0x41, 0x55] (PushPre 0x102525 2) (pushR64Effect 0x102525 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102525 2 13).toInstrSpec (push_r64_rex_effect_step 0x102525 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x102527 [0x41, 0x54] (PushPre 0x102527 2) (pushR64Effect 0x102527 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102527 2 12).toInstrSpec (push_r64_rex_effect_step 0x102527 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x102529 [0x53] (PushPre 0x102529 1) (pushR64Effect 0x102529 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102529 1 3).toInstrSpec (push_r64_effect_step 0x102529 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10252a [0x48, 0x81, 0xEC, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10252a) (subR64Imm32Effect 0x10252a 4 0x98)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10252a 4 0x98).toInstrSpec (sub_r64_imm32_effect_step 0x10252a 0x48 0xec 0x98 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x102531 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x102531) (movR64R64Effect 0x102531 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x102531 3 7).toInstrSpec (mov_r64_r64_effect_step 0x102531 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x102534 [0x48, 0xB8, 0xE0, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102534) (movR64Imm64Effect 0x102534 0 0xfffffffe0)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x102534 0 0xfffffffe0).toInstrSpec (mov_r64_imm64_effect_step 0x102534 0x48 0xb8 (by decide) (by decide) 0xfffffffe0) pre_rip
  have f9 : InstrSpec 0x10253e [0x4D, 0x8B, 0x61, 0x10] (LoadPre 0x10253e (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x10253e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10253e 12 (.base 9 (.d8 0x10)))
      [.gpr 9] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x10253e 12 (.base 9 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10253e 0x4d (by decide) 4 (.base 9 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x102542 [0x49, 0x39, 0xC4] (fun s => s.RIP = 0x102542) (cmpR64R64Effect 0x102542 12 0)
      [.gpr 12, .gpr 0] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x102542 12 0).toInstrSpec (cmp_r64_r64_effect_step 0x102542 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x102545 [0x0F, 0x97, 0xC0] (fun s => s.RIP = 0x102545) (atFlags (condHolds 7) (setccR8Effect 0x102545 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x102545 3 0 7).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x102545 7 0xc0 (by decide) (by decide) c)) pre_rip
  have f12 : InstrSpec 0x102548 [0x4C, 0x89, 0xC7] (fun s => s.RIP = 0x102548) (movR64R64Effect 0x102548 7 8)
      [.gpr 8] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102548 7 8).toInstrSpec (mov_r64_r64_effect_step 0x102548 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10254b [0x48, 0xC1, 0xEF, 0x3D] (fun s => s.RIP = 0x10254b) (shrR64Effect 0x10254b 4 7 61)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x10254b 4 7 61).toInstrSpec (shr_r64_imm8_effect_step 0x10254b 0x48 0xef 0x3d (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10254f [0x40, 0x0F, 0x95, 0xC7] (fun s => s.RIP = 0x10254f) (atFlags (condHolds 5) (setccR8Effect 0x10254f 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x10254f 4 7 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x10254f 5 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f15 : InstrSpec 0x102553 [0x40, 0x08, 0xC7] (fun s => s.RIP = 0x102553) (orR8R8Effect 0x102553 3 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (orR8R8Effect_footprint 0x102553 3 7 0).toInstrSpec (or_r8_r8_rex_effect_step 0x102553 0x40 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102521) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102523) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102525) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102527) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102529) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10252a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102531) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102534) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10253e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102542) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (16, 73), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102545) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (16, 73), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102548) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 76), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 78), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (16, 73), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10254b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 81) f13 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x10254b 4 7 61 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 82) (ρ' := [(0, 76), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 80), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10254f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 76), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 83), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102553) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f15 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 76), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 85), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102556) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 88) (jcc_rel8_effect_step 0x102556 4 0x8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102520 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102520 :=
  Rest.liftedBlock (rest_l102520 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102520 x hx)

theorem rest_l102558 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102558 bytes_l102558) (entryMap (live .l102558))
      2 0x102558 bytes_l102558 b_l102558 := by
  have f0 : InstrSpec 0x102558 [0xC6, 0x03, 0x01] (StorePre 0x102558 3 (fun s => AddrMode.addr (.base 3 .none) s (0x102558 + BitVec.ofNat 64 3)) 1) (movM8Imm8Effect 0x102558 (.base 3 .none) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x102558 (.base 3 .none) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x102558 (.base 3 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10255b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 54) (jmp_rel32_effect_step 0x10255b 0x1aa (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l102558 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102558 :=
  Rest.liftedBlock (rest_l102558 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102558 x hx)

theorem rest_l102560 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102560 bytes_l102560) (entryMap (live .l102560))
      19 0x102560 bytes_l102560 b_l102560 := by
  have f0 : InstrSpec 0x102560 [0x4D, 0x89, 0xCE] (fun s => s.RIP = 0x102560) (movR64R64Effect 0x102560 14 9)
      [.gpr 9] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x102560 14 9).toInstrSpec (mov_r64_r64_effect_step 0x102560 0x4d 0xce (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102563 [0x48, 0x89, 0x5C, 0x24, 0x58] (StorePre 0x102563 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x102563 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102563 3 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102563 3 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x102563 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x102568 [0x48, 0x89, 0x4C, 0x24, 0x68] (StorePre 0x102568 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x102568 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102568 1 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102568 1 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x102568 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10256d [0x4C, 0x89, 0x44, 0x24, 0x70] (StorePre 0x10256d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10256d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10256d 8 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10256d 8 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x10256d 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x102572 [0x44, 0x8B, 0x2A] (LoadPre 0x102572 (fun s => AddrMode.addr (.base 2 .none) s (0x102572 + BitVec.ofNat 64 3)) 4) (movR32M32Effect 0x102572 13 (.base 2 .none))
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR32M32Effect_footprint 0x102572 13 (.base 2 .none)).toInstrSpec (mov_r32_m32_effect_step 0x102572 0x44 (by decide) 5 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x102575 [0x44, 0x8B, 0x7A, 0x04] (LoadPre 0x102575 (fun s => AddrMode.addr (.base 2 (.d8 0x4)) s (0x102575 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x102575 15 (.base 2 (.d8 0x4)))
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x102575 15 (.base 2 (.d8 0x4))).toInstrSpec (mov_r32_m32_effect_step 0x102575 0x44 (by decide) 7 (.base 2 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x102579 [0x8B, 0x5A, 0x08] (LoadPre 0x102579 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x102579 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x102579 3 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR32M32LowEffect_footprint 0x102579 3 (.base 2 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x102579 3 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10257c [0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10257c 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10257c + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10257c (.sib 4 none 0 (.d32 0x80)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10257c (.sib 4 none 0 (.d32 0x80)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10257c 0x48 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x102588 [0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102588 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x102588 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102588 (.sib 4 none 0 (.d8 0x78)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102588 (.sib 4 none 0 (.d8 0x78)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102588 0x48 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x102591 [0x48, 0x89, 0x74, 0x24, 0x60] (StorePre 0x102591 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x102591 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102591 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102591 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x102591 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x102596 [0x48, 0x8D, 0x6E, 0x20] (fun s => s.RIP = 0x102596) (leaR64Effect 0x102596 5 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x102596 5 (.base 6 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x102596 0x48 (by decide) 5 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10259a [0x44, 0x89, 0x6C, 0x24, 0x10] (StorePre 0x10259a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10259a + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10259a 13 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x10259a 13 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m32_r32_effect_step 0x10259a 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10259f [0x44, 0x89, 0x7C, 0x24, 0x14] (StorePre 0x10259f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x10259f + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10259f 15 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x10259f 15 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m32_r32_effect_step 0x10259f 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1025a4 [0x89, 0x5C, 0x24, 0x18] (StorePre 0x1025a4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1025a4 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1025a4 3 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1025a4 3 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m32_r32_low_effect_step 0x1025a4 3 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1025a8 [0xC7, 0x44, 0x24, 0x1C, 0x00, 0x00, 0x00, 0x01] (StorePre 0x1025a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1025a8 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x1025a8 8 (.sib 4 none 0 (.d8 0x1c)) 0x1000000)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1025a8 8 (.sib 4 none 0 (.d8 0x1c)) 0x1000000).toInstrSpec (mov_m32_imm32_effect_step 0x1025a8 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide) 0x1000000) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1025b0 [0x48, 0x8D, 0x7C, 0x24, 0x78] (fun s => s.RIP = 0x1025b0) (leaR64Effect 0x1025b0 7 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1025b0 7 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x1025b0 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1025b5 [0x48, 0x8D, 0x54, 0x24, 0x10] (fun s => s.RIP = 0x1025b5) (leaR64Effect 0x1025b5 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1025b5 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1025b5 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1025ba [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x1025ba) (movR64R64Effect 0x1025ba 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1025ba 6 5).toInstrSpec (mov_r64_r64_effect_step 0x1025ba 0x48 0xee (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1025bd [0xE8, 0x3E, 0x2B, 0x00, 0x00] (PushPre 0x1025bd 5) (callEffect (fun _ => 0x105100) 0x1025c2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1025bd 0x105100 0x1025c2).toInstrSpec (call_rel32_effect_step 0x1025bd 0x2b3e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102563) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102568) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10256d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102572) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102575) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102579) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10257c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102588) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102591) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102596) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (5, 67), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10259a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (5, 67), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10259f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (5, 67), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025a4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (5, 67), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025a8) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (5, 67), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025b0) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (5, 67), (6, 6), (7, 73), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025b5) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 75), (3, 62), (4, 4), (5, 67), (6, 6), (7, 73), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025ba) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 1), (2, 75), (3, 62), (4, 4), (5, 67), (6, 77), (7, 73), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025bd) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 1), (2, 75), (3, 62), (4, 79), (5, 67), (6, 77), (7, 73), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105100) f18 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 81) (by decide) (by decide) rfl rfl

theorem block_l102560 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102560 :=
  Rest.liftedBlock (rest_l102560 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102560 x hx)

theorem rest_l1025c2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1025c2 bytes_l1025c2) (entryMap (live .l1025c2))
      12 0x1025c2 bytes_l1025c2 b_l1025c2 := by
  have f0 : InstrSpec 0x1025c2 [0x48, 0x89, 0x6C, 0x24, 0x30] (StorePre 0x1025c2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1025c2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1025c2 5 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1025c2 5 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1025c2 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1025c7 [0x4C, 0x89, 0xE5] (fun s => s.RIP = 0x1025c7) (movR64R64Effect 0x1025c7 5 12)
      [.gpr 12] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x1025c7 5 12).toInstrSpec (mov_r64_r64_effect_step 0x1025c7 0x4c 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1025ca [0x48, 0x8D, 0x4C, 0x24, 0x38] (fun s => s.RIP = 0x1025ca) (leaR64Effect 0x1025ca 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x1025ca 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x1025ca 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1025cf [0x44, 0x89, 0x6C, 0x24, 0x38] (StorePre 0x1025cf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1025cf + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1025cf 13 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1025cf 13 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m32_r32_effect_step 0x1025cf 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1025d4 [0x44, 0x89, 0x7C, 0x24, 0x3C] (StorePre 0x1025d4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x1025d4 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1025d4 15 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1025d4 15 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_m32_r32_effect_step 0x1025d4 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1025d9 [0x89, 0x5C, 0x24, 0x40] (StorePre 0x1025d9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1025d9 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1025d9 3 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1025d9 3 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m32_r32_low_effect_step 0x1025d9 3 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1025dd [0x48, 0xB8, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1025dd) (movR64Imm64Effect 0x1025dd 0 0x100000001)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x1025dd 0 0x100000001).toInstrSpec (mov_r64_imm64_effect_step 0x1025dd 0x48 0xb8 (by decide) (by decide) 0x100000001) pre_rip
  have f7 : InstrSpec 0x1025e7 [0x48, 0x89, 0x44, 0x24, 0x44] (StorePre 0x1025e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x1025e7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1025e7 0 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1025e7 0 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_m64_r64_effect_step 0x1025e7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1025ec [0x4D, 0x8B, 0x3E] (LoadPre 0x1025ec (fun s => AddrMode.addr (.base 14 .none) s (0x1025ec + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1025ec 15 (.base 14 .none))
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x1025ec 15 (.base 14 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1025ec 0x4d (by decide) 7 (.base 14 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1025ef [0x4D, 0x8B, 0x6E, 0x08] (LoadPre 0x1025ef (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1025ef + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1025ef 13 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x1025ef 13 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1025ef 0x4d (by decide) 5 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1025f3 [0x49, 0x83, 0xFC, 0x11] (fun s => s.RIP = 0x1025f3) (cmpR64Imm8Effect 0x1025f3 12 0x11)
      [.gpr 12] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1025f3 12 0x11).toInstrSpec (cmp_r64_imm8_effect_step 0x1025f3 0x49 0xfc 0x11 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025c7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025ca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025cf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025d4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025d9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025dd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025e7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025ec) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 61), (1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025ef) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 61), (1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 66), (14, 14), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025f3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 61), (1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 66), (14, 14), (15, 64), (16, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025f7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 70) (jcc_rel8_effect_step 0x1025f7 2 0x56) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1025c2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1025c2 :=
  Rest.liftedBlock (rest_l1025c2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1025c2 x hx)

theorem rest_l1025f9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1025f9 bytes_l1025f9) (entryMap (live .l1025f9))
      16 0x1025f9 bytes_l1025f9 b_l1025f9 := by
  have f0 : InstrSpec 0x1025f9 [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x1025f9) (movR64R64Effect 0x1025f9 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1025f9 0 5).toInstrSpec (mov_r64_r64_effect_step 0x1025f9 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1025fc [0x48, 0xC1, 0xE8, 0x04] (fun s => s.RIP = 0x1025fc) (shrR64Effect 0x1025fc 4 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x1025fc 4 0 4).toInstrSpec (shr_r64_imm8_effect_step 0x1025fc 0x48 0xe8 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102600 [0x49, 0xBC, 0xE0, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102600) (movR64Imm64Effect 0x102600 12 0xfffffffe0)
      [] [] [.reg 12, .rip] :=
    (movR64Imm64Effect_footprint 0x102600 12 0xfffffffe0).toInstrSpec (mov_r64_imm64_effect_step 0x102600 0x49 0xbc (by decide) (by decide) 0xfffffffe0) pre_rip
  have f3 : InstrSpec 0x10260a [0x49, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x10260a) (addR64Imm8Effect 0x10260a 12 0x10)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10260a 12 0x10).toInstrSpec (add_r64_imm8_effect_step 0x10260a 0x49 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10260e [0x49, 0x21, 0xEC] (fun s => s.RIP = 0x10260e) (andR64R64Effect 0x10260e 12 5)
      [.gpr 12, .gpr 5] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10260e 12 5).toInstrSpec (and_r64_r64_effect_step 0x10260e 0x49 0xec (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x102611 [0x41, 0x89, 0xEE] (fun s => s.RIP = 0x102611) (movR32R32Effect 0x102611 3 14 5)
      [.gpr 5] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x102611 3 14 5).toInstrSpec (mov_r32_r32_rex_effect_step 0x102611 0x41 0xee (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x102614 [0x41, 0x83, 0xE6, 0x0F] (fun s => s.RIP = 0x102614) (andR32Imm8Effect 0x102614 4 14 0xf)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x102614 4 14 0xf).toInstrSpec (and_r32_imm8_rex_effect_step 0x102614 0x41 0xe6 0xf (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x102618 [0x4B, 0x8D, 0x1C, 0x27] (fun s => s.RIP = 0x102618) (leaR64Effect 0x102618 3 (.sib 15 (some 12) 0 .none))
      [.gpr 15, .gpr 12] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x102618 3 (.sib 15 (some 12) 0 .none)).toInstrSpec (lea_r64_effect_step 0x102618 0x4b (by decide) 3 (.sib 15 (some 12) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10261c [0x4D, 0x01, 0xEC] (fun s => s.RIP = 0x10261c) (addR64R64Effect 0x10261c 12 13)
      [.gpr 12, .gpr 13] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10261c 12 13).toInstrSpec (add_r64_r64_effect_step 0x10261c 0x4d 0xec (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10261f [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x10261f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10261f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10261f 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10261f 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10261f 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x102624 [0x4C, 0x89, 0x7C, 0x24, 0x18] (StorePre 0x102624 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102624 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102624 15 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102624 15 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x102624 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x102629 [0x4C, 0x89, 0x6C, 0x24, 0x20] (StorePre 0x102629 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x102629 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102629 13 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102629 13 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x102629 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10262e [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x10262e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10262e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10262e 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10262e 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10262e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x102633 [0x48, 0x8D, 0x7C, 0x24, 0x30] (fun s => s.RIP = 0x102633) (leaR64Effect 0x102633 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102633 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x102633 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x102638 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x102638) (leaR64Effect 0x102638 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102638 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x102638 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10263d [0xE8, 0x0E, 0x4A, 0x00, 0x00] (PushPre 0x10263d 5) (callEffect (fun _ => 0x107050) 0x102642)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10263d 0x107050 0x102642).toInstrSpec (call_rel32_effect_step 0x10263d 0x4a0e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (4, 4), (5, 5), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1025fc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102600) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (11, 11), (12, 57), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10260a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (11, 11), (12, 59), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10260e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (11, 11), (12, 61), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102611) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (11, 11), (12, 61), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102614) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (11, 11), (12, 61), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102618) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 4), (5, 5), (11, 11), (12, 61), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10261c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 4), (5, 5), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10261f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 4), (5, 5), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102624) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 4), (5, 5), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102629) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 4), (5, 5), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10262e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 4), (5, 5), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102633) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 4), (5, 5), (7, 75), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102638) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 4), (5, 5), (6, 77), (7, 75), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10263d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 79), (5, 5), (6, 77), (7, 75), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107050) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 81) (by decide) (by decide) rfl rfl

theorem block_l1025f9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1025f9 :=
  Rest.liftedBlock (rest_l1025f9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1025f9 x hx)

theorem rest_l102642 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102642 bytes_l102642) (entryMap (live .l102642))
      3 0x102642 bytes_l102642 b_l102642 := by
  have f0 : InstrSpec 0x102642 [0x49, 0x89, 0xDF] (fun s => s.RIP = 0x102642) (movR64R64Effect 0x102642 15 3)
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x102642 15 3).toInstrSpec (mov_r64_r64_effect_step 0x102642 0x49 0xdf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102645 [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x102645) (testR64R64Effect 0x102645 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x102645 14 14).toInstrSpec (test_r64_r64_effect_step 0x102645 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102645) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102648) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x102648 5 0x14) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102642 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102642 :=
  Rest.liftedBlock (rest_l102642 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102642 x hx)

theorem rest_l10264a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10264a bytes_l10264a) (entryMap (live .l10264a))
      1 0x10264a bytes_l10264a b_l10264a := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x10264a 0x8f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10264a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10264a :=
  Rest.liftedBlock (rest_l10264a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10264a x hx)

theorem rest_l10264f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10264f bytes_l10264f) (entryMap (live .l10264f))
      4 0x10264f bytes_l10264f b_l10264f := by
  have f0 : InstrSpec 0x10264f [0x4D, 0x89, 0xEC] (fun s => s.RIP = 0x10264f) (movR64R64Effect 0x10264f 12 13)
      [.gpr 13] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10264f 12 13).toInstrSpec (mov_r64_r64_effect_step 0x10264f 0x4d 0xec (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102652 [0x49, 0x89, 0xEE] (fun s => s.RIP = 0x102652) (movR64R64Effect 0x102652 14 5)
      [.gpr 5] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x102652 14 5).toInstrSpec (mov_r64_r64_effect_step 0x102652 0x49 0xee (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102655 [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x102655) (testR64R64Effect 0x102655 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x102655 14 14).toInstrSpec (test_r64_r64_effect_step 0x102655 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 53), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102652) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 53), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102655) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 53), (13, 13), (14, 55), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102658) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x102658 4 0x80) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10264f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10264f :=
  Rest.liftedBlock (rest_l10264f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10264f x hx)

theorem rest_l10265e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10265e bytes_l10265e) (entryMap (live .l10265e))
      9 0x10265e bytes_l10265e b_l10265e := by
  have f0 : InstrSpec 0x10265e [0xB8, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10265e) (movR32Imm32Effect 0x10265e 5 0 0x10)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x10265e 5 0 0x10).toInstrSpec (mov_r32_imm32_effect_step 0x10265e 0xb8 (by decide) 0x10) pre_rip
  have f1 : InstrSpec 0x102663 [0x4C, 0x29, 0xF0] (fun s => s.RIP = 0x102663) (subR64R64Effect 0x102663 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x102663 0 14).toInstrSpec (sub_r64_r64_effect_step 0x102663 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102666 [0x31, 0xD2] (fun s => s.RIP = 0x102666) (xorR32R32Effect 0x102666 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x102666 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x102666 0xd2 (by decide)) pre_rip
  have f3 : InstrSpec 0x102668 [0x49, 0x83, 0xFE, 0x10] (fun s => s.RIP = 0x102668) (cmpR64Imm8Effect 0x102668 14 0x10)
      [.gpr 14] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x102668 14 0x10).toInstrSpec (cmp_r64_imm8_effect_step 0x102668 0x49 0xfe 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10266c [0x48, 0x0F, 0x42, 0xD0] (fun s => s.RIP = 0x10266c) (atFlags (condHolds 2) (cmovR64R64Effect 0x10266c 4 2 0))
      [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x10266c 4 2 0 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10266c 2 0x48 (by decide) 0xd0 (by decide) c)) pre_rip
  have f5 : InstrSpec 0x102670 [0x4A, 0x8D, 0x3C, 0x34] (fun s => s.RIP = 0x102670) (leaR64Effect 0x102670 7 (.sib 4 (some 14) 0 .none))
      [.gpr 4, .gpr 14] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102670 7 (.sib 4 (some 14) 0 .none)).toInstrSpec (lea_r64_effect_step 0x102670 0x4a (by decide) 7 (.sib 4 (some 14) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x102674 [0x48, 0x81, 0xC7, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102674) (addR64Imm32Effect 0x102674 7 0x88)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x102674 7 0x88).toInstrSpec (add_r64_imm32_effect_step 0x102674 0x48 0xc7 0x88 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10267b [0x31, 0xF6] (fun s => s.RIP = 0x10267b) (xorR32R32Effect 0x10267b 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10267b 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x10267b 0xf6 (by decide)) pre_rip
  have f8 : InstrSpec 0x10267d [0xFF, 0x15, 0xA5, 0xEB, 0x0F, 0x00] (GoesTo (CallMemPre 0x10267d (.rip 0xfeba5)) (callEffect (callMemPtr 0x10267d (.rip 0xfeba5)) (0x10267d + BitVec.ofNat 64 (callMemLen (.rip 0xfeba5)))) 0x103eb0) (callEffect (callMemPtr 0x10267d (.rip 0xfeba5)) (0x10267d + BitVec.ofNat 64 (callMemLen (.rip 0xfeba5))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x10267d (.rip 0xfeba5)).toInstrSpec (call_m64_effect_step 0x10267d (.rip 0xfeba5) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103eb0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102663) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102666) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102668) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10266c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102670) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102674) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10267b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10267d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eb0) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l10265e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10265e :=
  Rest.liftedBlock (rest_l10265e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10265e x hx)

theorem rest_l102683 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102683 bytes_l102683) (entryMap (live .l102683))
      7 0x102683 bytes_l102683 b_l102683 := by
  have f0 : InstrSpec 0x102683 [0x4C, 0x89, 0x6C, 0x24, 0x50] (StorePre 0x102683 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x102683 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102683 13 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102683 13 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x102683 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x102688 [0x4C, 0x8D, 0xAC, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102688) (leaR64Effect 0x102688 13 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x102688 13 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x102688 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102690 [0x48, 0x8D, 0x1D, 0x69, 0x18, 0x00, 0x00] (fun s => s.RIP = 0x102690) (leaR64Effect 0x102690 3 (.rip 0x1869))
      [] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x102690 3 (.rip 0x1869)).toInstrSpec (lea_r64_effect_step 0x102690 0x48 (by decide) 3 (.rip 0x1869) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102697 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x102697) (movR64R64Effect 0x102697 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102697 7 13).toInstrSpec (mov_r64_r64_effect_step 0x102697 0x4c 0xef (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10269a [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10269a) (movR64R64Effect 0x10269a 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10269a 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10269a 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10269d [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x10269d) (movR64R64Effect 0x10269d 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10269d 2 14).toInstrSpec (mov_r64_r64_effect_step 0x10269d 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1026a0 [0xFF, 0xD3] (GoesTo (CallPre 0x1026a0 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x1026a2) 0x103f00) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x1026a2)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x1026a0 3 0x1026a2).toInstrSpec (call_r64_effect_step 0x1026a0 0xd3 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 3 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102688) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102690) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(3, 56), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102697) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(3, 56), (4, 4), (5, 5), (7, 58), (9, 9), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10269a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 56), (4, 4), (5, 5), (6, 60), (7, 58), (9, 9), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10269d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(2, 62), (3, 56), (4, 4), (5, 5), (6, 60), (7, 58), (9, 9), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026a0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 62), (3, 56), (4, 64), (5, 5), (6, 60), (7, 58), (9, 9), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f6 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l102683 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102683 :=
  Rest.liftedBlock (rest_l102683 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102683 x hx)

theorem rest_l1026a2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1026a2 bytes_l1026a2) (entryMap (live .l1026a2))
      8 0x1026a2 bytes_l1026a2 b_l1026a2 := by
  have f0 : InstrSpec 0x1026a2 [0x48, 0x8D, 0x44, 0x24, 0x38] (fun s => s.RIP = 0x1026a2) (leaR64Effect 0x1026a2 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1026a2 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x1026a2 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1026a7 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x1026a7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1026a7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1026a7 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1026a7 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1026a7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1026ac [0x4C, 0x89, 0x6C, 0x24, 0x18] (StorePre 0x1026ac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1026ac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1026ac 13 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1026ac 13 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1026ac 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1026b1 [0x4C, 0x89, 0x6C, 0x24, 0x20] (StorePre 0x1026b1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1026b1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1026b1 13 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1026b1 13 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1026b1 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1026b6 [0x48, 0xC7, 0x44, 0x24, 0x28, 0x01, 0x00, 0x00, 0x00] (StorePre 0x1026b6 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1026b6 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1026b6 (.sib 4 none 0 (.d8 0x28)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1026b6 (.sib 4 none 0 (.d8 0x28)) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x1026b6 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1026bf [0x48, 0x8D, 0x7C, 0x24, 0x30] (fun s => s.RIP = 0x1026bf) (leaR64Effect 0x1026bf 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1026bf 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x1026bf 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1026c4 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x1026c4) (leaR64Effect 0x1026c4 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1026c4 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1026c4 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1026c9 [0xE8, 0x82, 0x49, 0x00, 0x00] (PushPre 0x1026c9 5) (callEffect (fun _ => 0x107050) 0x1026ce)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1026c9 0x107050 0x1026ce).toInstrSpec (call_rel32_effect_step 0x1026c9 0x4982 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026a7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026ac) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026b1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026b6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026bf) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026c4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 61), (7, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026c9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 63), (5, 5), (6, 61), (7, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107050) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l1026a2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1026a2 :=
  Rest.liftedBlock (rest_l1026a2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1026a2 x hx)

theorem rest_l1026ce [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1026ce bytes_l1026ce) (entryMap (live .l1026ce))
      5 0x1026ce bytes_l1026ce b_l1026ce := by
  have f0 : InstrSpec 0x1026ce [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x1026ce) (movR64R64Effect 0x1026ce 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1026ce 7 12).toInstrSpec (mov_r64_r64_effect_step 0x1026ce 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1026d1 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x1026d1) (movR64R64Effect 0x1026d1 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1026d1 6 13).toInstrSpec (mov_r64_r64_effect_step 0x1026d1 0x4c 0xee (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1026d4 [0x4C, 0x8B, 0x6C, 0x24, 0x50] (LoadPre 0x1026d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1026d4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026d4 13 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x1026d4 13 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x1026d4 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1026d9 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x1026d9) (movR64R64Effect 0x1026d9 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1026d9 2 14).toInstrSpec (mov_r64_r64_effect_step 0x1026d9 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1026dc [0xFF, 0xD3] (GoesTo (CallPre 0x1026dc 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x1026de) 0x103f00) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x1026de)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x1026dc 3 0x1026de).toInstrSpec (call_r64_effect_step 0x1026dc 0xd3 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 3 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026d1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026d4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026d9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026dc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 3), (4, 61), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l1026ce [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1026ce :=
  Rest.liftedBlock (rest_l1026ce code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1026ce x hx)

theorem rest_l1026de [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1026de bytes_l1026de) (entryMap (live .l1026de))
      9 0x1026de bytes_l1026de b_l1026de := by
  have f0 : InstrSpec 0x1026de [0x48, 0x8B, 0x5C, 0x24, 0x58] (LoadPre 0x1026de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1026de + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026de 3 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1026de 3 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x1026de 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1026e3 [0x48, 0x8D, 0x7B, 0x01] (fun s => s.RIP = 0x1026e3) (leaR64Effect 0x1026e3 7 (.base 3 (.d8 0x1)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1026e3 7 (.base 3 (.d8 0x1))).toInstrSpec (lea_r64_effect_step 0x1026e3 0x48 (by decide) 7 (.base 3 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1026e7 [0x48, 0x89, 0x2C, 0x24] (StorePre 0x1026e7 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1026e7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1026e7 5 (.sib 4 none 0 .none))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1026e7 5 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1026e7 0x48 (by decide) 5 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1026eb [0x48, 0x8D, 0x54, 0x24, 0x78] (fun s => s.RIP = 0x1026eb) (leaR64Effect 0x1026eb 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1026eb 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x1026eb 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1026f0 [0x48, 0x8B, 0x74, 0x24, 0x60] (LoadPre 0x1026f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1026f0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026f0 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1026f0 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x1026f0 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1026f5 [0x48, 0x8B, 0x4C, 0x24, 0x68] (LoadPre 0x1026f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1026f5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026f5 1 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1026f5 1 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x1026f5 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1026fa [0x4C, 0x8B, 0x44, 0x24, 0x70] (LoadPre 0x1026fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1026fa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026fa 8 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1026fa 8 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x1026fa 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1026ff [0x4D, 0x89, 0xE9] (fun s => s.RIP = 0x1026ff) (movR64R64Effect 0x1026ff 9 13)
      [.gpr 13] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x1026ff 9 13).toInstrSpec (mov_r64_r64_effect_step 0x1026ff 0x4d 0xe9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x102702 [0xE8, 0xF9, 0xF0, 0xFF, 0xFF] (PushPre 0x102702 5) (callEffect (fun _ => 0x101800) 0x102707)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102702 0x101800 0x102707).toInstrSpec (call_rel32_effect_step 0x102702 0xfffff0f9 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026e3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (7, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026e7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 53), (4, 4), (5, 5), (7, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026eb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 58), (3, 53), (4, 4), (5, 5), (7, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026f0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 58), (3, 53), (4, 4), (5, 5), (6, 60), (7, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026f5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 62), (2, 58), (3, 53), (4, 4), (5, 5), (6, 60), (7, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026fa) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 62), (2, 58), (3, 53), (4, 4), (5, 5), (6, 60), (7, 55), (8, 64), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1026ff) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 62), (2, 58), (3, 53), (4, 4), (5, 5), (6, 60), (7, 55), (8, 64), (9, 66), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102702) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 62), (2, 58), (3, 53), (4, 68), (5, 5), (6, 60), (7, 55), (8, 64), (9, 66), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101800) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 70) (by decide) (by decide) rfl rfl

theorem block_l1026de [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1026de :=
  Rest.liftedBlock (rest_l1026de code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1026de x hx)

theorem rest_l102707 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102707 bytes_l102707) (entryMap (live .l102707))
      1 0x102707 bytes_l102707 b_l102707 := by
  have f0 : InstrSpec 0x102707 [0xC6, 0x03, 0x00] (StorePre 0x102707 3 (fun s => AddrMode.addr (.base 3 .none) s (0x102707 + BitVec.ofNat 64 3)) 1) (movM8Imm8Effect 0x102707 (.base 3 .none) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x102707 (.base 3 .none) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x102707 (.base 3 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10270a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l102707 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102707 :=
  Rest.liftedBlock (rest_l102707 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102707 x hx)

theorem rest_l10270a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10270a bytes_l10270a) (entryMap (live .l10270a))
      9 0x10270a bytes_l10270a b_l10270a := by
  have f0 : InstrSpec 0x10270a [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10270a) (movR64R64Effect 0x10270a 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10270a 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10270a 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10270d [0x48, 0x81, 0xC4, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10270d) (addR64Imm32Effect 0x10270d 4 0x98)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x10270d 4 0x98).toInstrSpec (add_r64_imm32_effect_step 0x10270d 0x48 0xc4 0x98 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102714 [0x5B] (PopPre 0x102714) (popR64Effect 0x102714 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102714 1 3).toInstrSpec (pop_r64_effect_step 0x102714 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x102715 [0x41, 0x5C] (PopPre 0x102715) (popR64Effect 0x102715 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102715 2 12).toInstrSpec (pop_r64_rex_effect_step 0x102715 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x102717 [0x41, 0x5D] (PopPre 0x102717) (popR64Effect 0x102717 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102717 2 13).toInstrSpec (pop_r64_rex_effect_step 0x102717 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x102719 [0x41, 0x5E] (PopPre 0x102719) (popR64Effect 0x102719 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102719 2 14).toInstrSpec (pop_r64_rex_effect_step 0x102719 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10271b [0x41, 0x5F] (PopPre 0x10271b) (popR64Effect 0x10271b 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10271b 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10271b 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x10271d [0x5D] (PopPre 0x10271d) (popR64Effect 0x10271d 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10271d 1 5).toInstrSpec (pop_r64_effect_step 0x10271d 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x10271e [0xC3] (RetPre 0x10271e) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10271e).toInstrSpec (ret_effect_step 0x10271e) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10270d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102714) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102715) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102717) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102719) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10271b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10271d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10271e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l10270a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10270a :=
  Rest.liftedBlock (rest_l10270a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10270a x hx)

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

theorem_by block_l102520_eval :
    program.runBlock (dialect code) ⟨.l102520, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102558_eval :
    program.runBlock (dialect code) ⟨.l102558, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102560_eval :
    program.runBlock (dialect code) ⟨.l102560, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1025c2_eval :
    program.runBlock (dialect code) ⟨.l1025c2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1025f9_eval :
    program.runBlock (dialect code) ⟨.l1025f9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102642_eval :
    program.runBlock (dialect code) ⟨.l102642, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10264a_eval :
    program.runBlock (dialect code) ⟨.l10264a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10264f_eval :
    program.runBlock (dialect code) ⟨.l10264f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10265e_eval :
    program.runBlock (dialect code) ⟨.l10265e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102683_eval :
    program.runBlock (dialect code) ⟨.l102683, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1026a2_eval :
    program.runBlock (dialect code) ⟨.l1026a2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1026ce_eval :
    program.runBlock (dialect code) ⟨.l1026ce, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1026de_eval :
    program.runBlock (dialect code) ⟨.l1026de, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102707_eval :
    program.runBlock (dialect code) ⟨.l102707, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10270a_eval :
    program.runBlock (dialect code) ⟨.l10270a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
