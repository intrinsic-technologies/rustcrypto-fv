import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l1084e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1084e0 bytes_l1084e0) (entryMap (live .l1084e0))
      14 0x1084e0 bytes_l1084e0 b_l1084e0 := by
  have f0 : InstrSpec 0x1084e0 [0x55] (PushPre 0x1084e0 1) (pushR64Effect 0x1084e0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1084e0 1 5).toInstrSpec (push_r64_effect_step 0x1084e0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1084e1 [0x41, 0x57] (PushPre 0x1084e1 2) (pushR64Effect 0x1084e1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1084e1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1084e1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1084e3 [0x41, 0x56] (PushPre 0x1084e3 2) (pushR64Effect 0x1084e3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1084e3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1084e3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1084e5 [0x41, 0x55] (PushPre 0x1084e5 2) (pushR64Effect 0x1084e5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1084e5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1084e5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1084e7 [0x41, 0x54] (PushPre 0x1084e7 2) (pushR64Effect 0x1084e7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1084e7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1084e7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1084e9 [0x53] (PushPre 0x1084e9 1) (pushR64Effect 0x1084e9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1084e9 1 3).toInstrSpec (push_r64_effect_step 0x1084e9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1084ea [0x48, 0x81, 0xEC, 0xD8, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x1084ea) (subR64Imm32Effect 0x1084ea 4 0x8d8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x1084ea 4 0x8d8).toInstrSpec (sub_r64_imm32_effect_step 0x1084ea 0x48 0xec 0x8d8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1084f1 [0x48, 0x89, 0xF3] (fun s => s.RIP = 0x1084f1) (movR64R64Effect 0x1084f1 3 6)
      [.gpr 6] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1084f1 3 6).toInstrSpec (mov_r64_r64_effect_step 0x1084f1 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1084f4 [0x48, 0x8B, 0x07] (LoadPre 0x1084f4 (fun s => AddrMode.addr (.base 7 .none) s (0x1084f4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1084f4 0 (.base 7 .none))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1084f4 0 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1084f4 0x48 (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1084f7 [0x31, 0xC9] (fun s => s.RIP = 0x1084f7) (xorR32R32Effect 0x1084f7 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1084f7 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x1084f7 0xc9 (by decide)) pre_rip
  have f10 : InstrSpec 0x1084f9 [0x48, 0xBA, 0x00, 0x10, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1084f9) (movR64Imm64Effect 0x1084f9 2 0x1000001000)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x1084f9 2 0x1000001000).toInstrSpec (mov_r64_imm64_effect_step 0x1084f9 0x48 0xba (by decide) (by decide) 0x1000001000) pre_rip
  have f11 : InstrSpec 0x108503 [0x48, 0xBE, 0x0F, 0x00, 0x0F, 0x00, 0x0F, 0x00, 0x0F, 0x00] (fun s => s.RIP = 0x108503) (movR64Imm64Effect 0x108503 6 0xf000f000f000f)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x108503 6 0xf000f000f000f).toInstrSpec (mov_r64_imm64_effect_step 0x108503 0x48 0xbe (by decide) (by decide) 0xf000f000f000f) pre_rip
  have f12 : InstrSpec 0x10850d [0x48, 0xBF, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11] (fun s => s.RIP = 0x10850d) (movR64Imm64Effect 0x10850d 7 0x1111111111111111)
      [] [] [.reg 7, .rip] :=
    (movR64Imm64Effect_footprint 0x10850d 7 0x1111111111111111).toInstrSpec (mov_r64_imm64_effect_step 0x10850d 0x48 0xbf (by decide) (by decide) 0x1111111111111111) pre_rip
  have f13 : InstrSpec 0x108517 [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108517) (fun _ => nopEffect 0x108517 9)
      [] [] [.rip] :=
    (nopEffect_footprint 0x108517 9).toInstrSpec (nop_m_effect_step 0x108517 [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084e1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084e3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084e5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084e7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084e9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084ea) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084f1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084f4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084f7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 71), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084f9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 69), (1, 71), (2, 73), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108503) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 69), (1, 71), (2, 73), (3, 67), (4, 65), (5, 5), (6, 75), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10850d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 69), (1, 71), (2, 73), (3, 67), (4, 65), (5, 5), (6, 75), (7, 77), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108517) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 69), (1, 71), (2, 73), (3, 67), (4, 65), (5, 5), (6, 75), (7, 77), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108520) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 80) (by decide) rfl

theorem block_l1084e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1084e0 :=
  Rest.liftedBlock (rest_l1084e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1084e0 x hx)

theorem rest_l108520_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x108520 bytes_l108520) [(0, 0), (1, 88), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 85), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x10856b bytes_l108520_1 b_l108520_1 := by
  exact Rest.jcc (n := 92) (jcc_rel8_effect_step 0x10856b 5 0xb3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l108520 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108520 bytes_l108520) (entryMap (live .l108520))
      21 0x108520 bytes_l108520 b_l108520 := by
  have f0 : InstrSpec 0x108520 [0x44, 0x0F, 0xB7, 0x04, 0x48] (LoadPre 0x108520 (fun s => AddrMode.addr (.sib 0 (some 1) 1 .none) s (0x108520 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x108520 5 8 (.sib 0 (some 1) 1 .none))
      [.gpr 0, .gpr 1] [] [.reg 8, .rip] :=
    (movzxR32M16Effect_footprint 0x108520 5 8 (.sib 0 (some 1) 1 .none)).toInstrSpec (movzx_r32_m16_rex_effect_step 0x108520 0x44 (by decide) 0 (.sib 0 (some 1) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x108525 [0x4D, 0x89, 0xC1] (fun s => s.RIP = 0x108525) (movR64R64Effect 0x108525 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x108525 9 8).toInstrSpec (mov_r64_r64_effect_step 0x108525 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x108528 [0x49, 0xC1, 0xE1, 0x18] (fun s => s.RIP = 0x108528) (shlR64Effect 0x108528 4 9 24)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR64Effect_footprint 0x108528 4 9 24).toInstrSpec (shl_r64_imm8_effect_step 0x108528 0x49 0xe1 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10852c [0x4D, 0x09, 0xC1] (fun s => s.RIP = 0x10852c) (orR64R64Effect 0x10852c 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10852c 9 8).toInstrSpec (or_r64_r64_effect_step 0x10852c 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10852f [0x4C, 0x0F, 0xAF, 0xC2] (fun s => s.RIP = 0x10852f) (imulR64R64Effect 0x10852f 4 8 2)
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x10852f 4 8 2).toInstrSpec (imul_r64_r64_effect_step 0x10852f 0x4c (by decide) 0xc2 (by decide)) pre_rip
  have f5 : InstrSpec 0x108533 [0x4D, 0x09, 0xC8] (fun s => s.RIP = 0x108533) (orR64R64Effect 0x108533 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108533 8 9).toInstrSpec (or_r64_r64_effect_step 0x108533 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x108536 [0x49, 0x21, 0xF0] (fun s => s.RIP = 0x108536) (andR64R64Effect 0x108536 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108536 8 6).toInstrSpec (and_r64_r64_effect_step 0x108536 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x108539 [0x4D, 0x89, 0xC1] (fun s => s.RIP = 0x108539) (movR64R64Effect 0x108539 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x108539 9 8).toInstrSpec (mov_r64_r64_effect_step 0x108539 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10853c [0x49, 0xC1, 0xE1, 0x06] (fun s => s.RIP = 0x10853c) (shlR64Effect 0x10853c 4 9 6)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR64Effect_footprint 0x10853c 4 9 6).toInstrSpec (shl_r64_imm8_effect_step 0x10853c 0x49 0xe1 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x108540 [0x4D, 0x09, 0xC1] (fun s => s.RIP = 0x108540) (orR64R64Effect 0x108540 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108540 9 8).toInstrSpec (or_r64_r64_effect_step 0x108540 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x108543 [0x4D, 0x89, 0xC2] (fun s => s.RIP = 0x108543) (movR64R64Effect 0x108543 10 8)
      [.gpr 8] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x108543 10 8).toInstrSpec (mov_r64_r64_effect_step 0x108543 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x108546 [0x49, 0xC1, 0xE2, 0x09] (fun s => s.RIP = 0x108546) (shlR64Effect 0x108546 4 10 9)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR64Effect_footprint 0x108546 4 10 9).toInstrSpec (shl_r64_imm8_effect_step 0x108546 0x49 0xe2 0x9 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10854a [0x4F, 0x8D, 0x04, 0xC2] (fun s => s.RIP = 0x10854a) (leaR64Effect 0x10854a 8 (.sib 10 (some 8) 3 .none))
      [.gpr 10, .gpr 8] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x10854a 8 (.sib 10 (some 8) 3 .none)).toInstrSpec (lea_r64_effect_step 0x10854a 0x4f (by decide) 0 (.sib 10 (some 8) 3 .none) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10854e [0x4D, 0x09, 0xC8] (fun s => s.RIP = 0x10854e) (orR64R64Effect 0x10854e 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10854e 8 9).toInstrSpec (or_r64_r64_effect_step 0x10854e 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x108551 [0x49, 0x21, 0xF8] (fun s => s.RIP = 0x108551) (andR64R64Effect 0x108551 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108551 8 7).toInstrSpec (and_r64_r64_effect_step 0x108551 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x108554 [0x4F, 0x8D, 0x04, 0x80] (fun s => s.RIP = 0x108554) (leaR64Effect 0x108554 8 (.sib 8 (some 8) 2 .none))
      [.gpr 8, .gpr 8] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x108554 8 (.sib 8 (some 8) 2 .none)).toInstrSpec (lea_r64_effect_step 0x108554 0x4f (by decide) 0 (.sib 8 (some 8) 2 .none) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x108558 [0x4F, 0x8D, 0x04, 0x40] (fun s => s.RIP = 0x108558) (leaR64Effect 0x108558 8 (.sib 8 (some 8) 1 .none))
      [.gpr 8, .gpr 8] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x108558 8 (.sib 8 (some 8) 1 .none)).toInstrSpec (lea_r64_effect_step 0x108558 0x4f (by decide) 0 (.sib 8 (some 8) 1 .none) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10855c [0x4C, 0x89, 0x84, 0xCC, 0x18, 0x05, 0x00, 0x00] (StorePre 0x10855c 8 (fun s => AddrMode.addr (.sib 4 (some 1) 3 (.d32 0x518)) s (0x10855c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10855c 8 (.sib 4 (some 1) 3 (.d32 0x518)))
      [.gpr 8, .gpr 4, .gpr 1] [] [.rip] :=
    (movM64R64Effect_footprint 0x10855c 8 (.sib 4 (some 1) 3 (.d32 0x518))).toInstrSpec (mov_m64_r64_effect_step 0x10855c 0x4c (by decide) 0 (.sib 4 (some 1) 3 (.d32 0x518)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x108564 [0x48, 0xFF, 0xC1] (fun s => s.RIP = 0x108564) (incR64Effect 0x108564 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (incR64Effect_footprint 0x108564 1).toInstrSpec (inc_r64_effect_step 0x108564 0x48 0xc1 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x108567 [0x48, 0x83, 0xF9, 0x78] (fun s => s.RIP = 0x108567) (cmpR64Imm8Effect 0x108567 1 0x78)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x108567 1 0x78).toInstrSpec (cmp_r64_imm8_effect_step 0x108567 0x48 0xf9 0x78 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108525) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108528) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10852c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10852f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 61), (9, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108533) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108536) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108539) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 67), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10853c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108540) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108543) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 71), (10, 73), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108546) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10854a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 77), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10854e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 79), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108551) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 81), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108554) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 83), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108558) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 85), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10855c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 85), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108564) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 88), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 85), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108567) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 0), (1, 88), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 85), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10856b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l108520_1 code

theorem block_l108520 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108520 :=
  Rest.liftedBlock (rest_l108520 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108520 x hx)

theorem rest_l10856d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10856d bytes_l10856d) (entryMap (live .l10856d))
      5 0x10856d bytes_l10856d b_l10856d := by
  have f0 : InstrSpec 0x10856d [0x48, 0x89, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00] (StorePre 0x10856d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x10856d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10856d 0 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10856d 0 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (mov_m64_r64_effect_step 0x10856d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x108575 [0x48, 0x8D, 0xBC, 0x24, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x108575) (leaR64Effect 0x108575 7 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x108575 7 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (lea_r64_effect_step 0x108575 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10857d [0x48, 0x8D, 0xB4, 0x24, 0x18, 0x05, 0x00, 0x00] (fun s => s.RIP = 0x10857d) (leaR64Effect 0x10857d 6 (.sib 4 none 0 (.d32 0x518)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10857d 6 (.sib 4 none 0 (.d32 0x518))).toInstrSpec (lea_r64_effect_step 0x10857d 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x518)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x108585 [0xBA, 0xC0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x108585) (movR32Imm32Effect 0x108585 5 2 0x3c0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x108585 5 2 0x3c0).toInstrSpec (mov_r32_imm32_effect_step 0x108585 0xba (by decide) 0x3c0) pre_rip
  have f4 : InstrSpec 0x10858a [0xFF, 0x15, 0x78, 0x8C, 0x0F, 0x00] (GoesTo (CallMemPre 0x10858a (.rip 0xf8c78)) (callEffect (callMemPtr 0x10858a (.rip 0xf8c78)) (0x10858a + BitVec.ofNat 64 (callMemLen (.rip 0xf8c78)))) 0x103f00) (callEffect (callMemPtr 0x10858a (.rip 0xf8c78)) (0x10858a + BitVec.ofNat 64 (callMemLen (.rip 0xf8c78))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x10858a (.rip 0xf8c78)).toInstrSpec (call_m64_effect_step 0x10858a (.rip 0xf8c78) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108575) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 54), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10857d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 56), (7, 54), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108585) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 58), (3, 3), (4, 4), (5, 5), (6, 56), (7, 54), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10858a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 58), (3, 3), (4, 60), (5, 5), (6, 56), (7, 54), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l10856d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10856d :=
  Rest.liftedBlock (rest_l10856d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10856d x hx)

theorem rest_l108590 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108590 bytes_l108590) (entryMap (live .l108590))
      14 0x108590 bytes_l108590 b_l108590 := by
  have f0 : InstrSpec 0x108590 [0x4C, 0x8B, 0x0B] (LoadPre 0x108590 (fun s => AddrMode.addr (.base 3 .none) s (0x108590 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x108590 9 (.base 3 .none))
      [.gpr 3] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x108590 9 (.base 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x108590 0x4c (by decide) 1 (.base 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x108593 [0x48, 0x8B, 0x43, 0x08] (LoadPre 0x108593 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x108593 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108593 0 (.base 3 (.d8 0x8)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108593 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x108593 0x48 (by decide) 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x108597 [0x48, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00] (StorePre 0x108597 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x108597 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108597 0 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108597 0 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x108597 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10859f [0x48, 0x8B, 0x53, 0x10] (LoadPre 0x10859f (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10859f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10859f 2 (.base 3 (.d8 0x10)))
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10859f 2 (.base 3 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10859f 0x48 (by decide) 2 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1085a3 [0x48, 0x8B, 0x43, 0x18] (LoadPre 0x1085a3 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1085a3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1085a3 0 (.base 3 (.d8 0x18)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1085a3 0 (.base 3 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1085a3 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1085a7 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x1085a7) (movR64R64Effect 0x1085a7 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1085a7 1 0).toInstrSpec (mov_r64_r64_effect_step 0x1085a7 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1085aa [0x48, 0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x1085aa) (shrR64Effect 0x1085aa 4 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x1085aa 4 1 2).toInstrSpec (shr_r64_imm8_effect_step 0x1085aa 0x48 0xe9 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1085ae [0x48, 0x89, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00] (StorePre 0x1085ae 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1085ae + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1085ae 0 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1085ae 0 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_m64_r64_effect_step 0x1085ae 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1085b6 [0x83, 0xE0, 0x03] (fun s => s.RIP = 0x1085b6) (andR32Imm8Effect 0x1085b6 3 0 0x3)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1085b6 3 0 0x3).toInstrSpec (and_r32_imm8_effect_step 0x1085b6 0xe0 0x3 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1085b9 [0x48, 0x89, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00] (StorePre 0x1085b9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1085b9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1085b9 0 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1085b9 0 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x1085b9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1085c1 [0x48, 0x89, 0x8C, 0x24, 0x48, 0x01, 0x00, 0x00] (StorePre 0x1085c1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x1085c1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1085c1 1 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1085c1 1 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (mov_m64_r64_effect_step 0x1085c1 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1085c9 [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x1085c9) (testR64R64Effect 0x1085c9 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1085c9 1 1).toInstrSpec (test_r64_r64_effect_step 0x1085c9 0x48 0xc9 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1085cc [0x4C, 0x89, 0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00] (StorePre 0x1085cc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x1085cc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1085cc 9 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1085cc 9 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x1085cc 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108593) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108597) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10859f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085a3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085a7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 62), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085aa) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 60), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085ae) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 60), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085b6) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085b9) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085c1) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085c9) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 67), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085cc) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 67), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085d4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jcc (n := 74) (jcc_rel32_effect_step 0x1085d4 4 0xf2f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l108590 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108590 :=
  Rest.liftedBlock (rest_l108590 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108590 x hx)

theorem rest_l1085da [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1085da bytes_l1085da) (entryMap (live .l1085da))
      3 0x1085da bytes_l1085da b_l1085da := by
  have f0 : InstrSpec 0x1085da [0x48, 0xC7, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1085da 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1085da + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1085da (.sib 4 none 0 (.d32 0xe0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1085da (.sib 4 none 0 (.d32 0xe0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1085da 0x48 (by decide) (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1085e6 [0x48, 0x89, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x1085e6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1085e6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1085e6 2 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1085e6 2 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x1085e6 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085e6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085ee) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x1085ee 0x8a5 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1085da [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1085da :=
  Rest.liftedBlock (rest_l1085da code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1085da x hx)

theorem rest_l108600_3 [Bindings] (code : CodeMap) :
    Rest (n := 166) code lifted (codeRange 0x108600 bytes_l108600) [(0, 0), (1, 1), (2, 164), (3, 74), (4, 4), (5, 56), (6, 151), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      20 0x1086df bytes_l108600_3 b_l108600_3 := by
  have f60 : InstrSpec 0x1086df [0x48, 0x31, 0xCA] (fun s => s.RIP = 0x1086df) (xorR64R64Effect 0x1086df 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1086df 2 1).toInstrSpec (xor_r64_r64_effect_step 0x1086df 0x48 0xca (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x1086e2 [0x4C, 0x21, 0xF2] (fun s => s.RIP = 0x1086e2) (andR64R64Effect 0x1086e2 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1086e2 2 14).toInstrSpec (and_r64_r64_effect_step 0x1086e2 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x1086e5 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x1086e5) (movR64R64Effect 0x1086e5 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1086e5 6 2).toInstrSpec (mov_r64_r64_effect_step 0x1086e5 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x1086e8 [0x48, 0xC1, 0xE6, 0x08] (fun s => s.RIP = 0x1086e8) (shlR64Effect 0x1086e8 4 6 8)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR64Effect_footprint 0x1086e8 4 6 8).toInstrSpec (shl_r64_imm8_effect_step 0x1086e8 0x48 0xe6 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x1086ec [0x48, 0x01, 0xD6] (fun s => s.RIP = 0x1086ec) (addR64R64Effect 0x1086ec 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1086ec 6 2).toInstrSpec (add_r64_r64_effect_step 0x1086ec 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x1086ef [0x48, 0x31, 0xCE] (fun s => s.RIP = 0x1086ef) (xorR64R64Effect 0x1086ef 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1086ef 6 1).toInstrSpec (xor_r64_r64_effect_step 0x1086ef 0x48 0xce (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x1086f2 [0x48, 0x89, 0x74, 0x24, 0x38] (StorePre 0x1086f2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1086f2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1086f2 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1086f2 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x1086f2 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f67 : InstrSpec 0x1086f7 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x1086f7) (movR64R64Effect 0x1086f7 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1086f7 1 0).toInstrSpec (mov_r64_r64_effect_step 0x1086f7 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x1086fa [0x48, 0xC1, 0xE9, 0x08] (fun s => s.RIP = 0x1086fa) (shrR64Effect 0x1086fa 4 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x1086fa 4 1 8).toInstrSpec (shr_r64_imm8_effect_step 0x1086fa 0x48 0xe9 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x1086fe [0x48, 0x31, 0xC1] (fun s => s.RIP = 0x1086fe) (xorR64R64Effect 0x1086fe 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1086fe 1 0).toInstrSpec (xor_r64_r64_effect_step 0x1086fe 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x108701 [0x4C, 0x21, 0xF1] (fun s => s.RIP = 0x108701) (andR64R64Effect 0x108701 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108701 1 14).toInstrSpec (and_r64_r64_effect_step 0x108701 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x108704 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x108704) (movR64R64Effect 0x108704 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x108704 2 1).toInstrSpec (mov_r64_r64_effect_step 0x108704 0x48 0xca (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x108707 [0x48, 0xC1, 0xE2, 0x08] (fun s => s.RIP = 0x108707) (shlR64Effect 0x108707 4 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR64Effect_footprint 0x108707 4 2 8).toInstrSpec (shl_r64_imm8_effect_step 0x108707 0x48 0xe2 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x10870b [0x48, 0x01, 0xCA] (fun s => s.RIP = 0x10870b) (addR64R64Effect 0x10870b 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10870b 2 1).toInstrSpec (add_r64_r64_effect_step 0x10870b 0x48 0xca (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x10870e [0x48, 0x31, 0xC2] (fun s => s.RIP = 0x10870e) (xorR64R64Effect 0x10870e 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10870e 2 0).toInstrSpec (xor_r64_r64_effect_step 0x10870e 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x108711 [0x48, 0x89, 0x54, 0x24, 0x40] (StorePre 0x108711 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x108711 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108711 2 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108711 2 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x108711 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f76 : InstrSpec 0x108716 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108716) (movR32Imm32Effect 0x108716 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x108716 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x108716 0xbe (by decide) 0x8) pre_rip
  have f77 : InstrSpec 0x10871b [0x48, 0x8D, 0x5C, 0x24, 0x08] (fun s => s.RIP = 0x10871b) (leaR64Effect 0x10871b 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x10871b 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10871b 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x108720 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x108720) (movR64R64Effect 0x108720 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x108720 7 3).toInstrSpec (mov_r64_r64_effect_step 0x108720 0x48 0xdf (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x108723 [0xE8, 0x68, 0x87, 0xFF, 0xFF] (PushPre 0x108723 5) (callEffect (fun _ => 0x100e90) 0x108728)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x108723 0x100e90 0x108728).toInstrSpec (call_rel32_effect_step 0x108723 0xffff8768 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f60 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 0), (1, 1), (2, 166), (3, 74), (4, 4), (5, 56), (6, 151), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086e2) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f61 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 0), (1, 1), (2, 168), (3, 74), (4, 4), (5, 56), (6, 151), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086e5) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f62 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 0), (1, 1), (2, 168), (3, 74), (4, 4), (5, 56), (6, 170), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086e8) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f63 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 0), (1, 1), (2, 168), (3, 74), (4, 4), (5, 56), (6, 172), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086ec) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f64 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 0), (1, 1), (2, 168), (3, 74), (4, 4), (5, 56), (6, 174), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086ef) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.out (n := 176) f65 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 177) (ρ' := [(0, 0), (1, 1), (2, 168), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086f2) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.exec (n := 178) (ρ' := [(0, 0), (1, 1), (2, 168), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086f7) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f67 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 0), (1, 179), (2, 168), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086fa) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f68 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 0), (1, 181), (2, 168), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086fe) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f69 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 0), (1, 183), (2, 168), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108701) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f70 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 0), (1, 185), (2, 168), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108704) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f71 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 0), (1, 185), (2, 187), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108707) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f72 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 0), (1, 185), (2, 189), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10870b) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f73 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 0), (1, 185), (2, 191), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10870e) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f74 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 0), (1, 185), (2, 193), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108711) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.exec (n := 195) (ρ' := [(0, 0), (1, 185), (2, 193), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108716) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 196) (RestInside.out (n := 196) f76 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 197) (ρ' := [(0, 0), (1, 185), (2, 193), (3, 74), (4, 4), (5, 56), (6, 196), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10871b) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 198) (RestInside.out (n := 198) f77 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 199) (ρ' := [(0, 0), (1, 185), (2, 193), (3, 198), (4, 4), (5, 56), (6, 196), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108720) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f78 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 0), (1, 185), (2, 193), (3, 198), (4, 4), (5, 56), (6, 196), (7, 200), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108723) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f79 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 0), (1, 185), (2, 193), (3, 198), (4, 202), (5, 56), (6, 196), (7, 200), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e90) f79 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 204) (by decide) (by decide) rfl rfl

theorem rest_l108600_2 [Bindings] (code : CodeMap) :
    Rest (n := 128) code lifted (codeRange 0x108600 bytes_l108600) [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 117), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      40 0x10869a bytes_l108600_2 b_l108600_2 := by
  have f40 : InstrSpec 0x10869a [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x10869a) (movR64R64Effect 0x10869a 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10869a 7 6).toInstrSpec (mov_r64_r64_effect_step 0x10869a 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x10869d [0x48, 0xC1, 0xEF, 0x08] (fun s => s.RIP = 0x10869d) (shrR64Effect 0x10869d 4 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x10869d 4 7 8).toInstrSpec (shr_r64_imm8_effect_step 0x10869d 0x48 0xef 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x1086a1 [0x48, 0x31, 0xF7] (fun s => s.RIP = 0x1086a1) (xorR64R64Effect 0x1086a1 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1086a1 7 6).toInstrSpec (xor_r64_r64_effect_step 0x1086a1 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x1086a4 [0x4C, 0x21, 0xF7] (fun s => s.RIP = 0x1086a4) (andR64R64Effect 0x1086a4 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1086a4 7 14).toInstrSpec (and_r64_r64_effect_step 0x1086a4 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x1086a7 [0x49, 0x89, 0xF8] (fun s => s.RIP = 0x1086a7) (movR64R64Effect 0x1086a7 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1086a7 8 7).toInstrSpec (mov_r64_r64_effect_step 0x1086a7 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x1086aa [0x49, 0xC1, 0xE0, 0x08] (fun s => s.RIP = 0x1086aa) (shlR64Effect 0x1086aa 4 8 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR64Effect_footprint 0x1086aa 4 8 8).toInstrSpec (shl_r64_imm8_effect_step 0x1086aa 0x49 0xe0 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x1086ae [0x49, 0x01, 0xF8] (fun s => s.RIP = 0x1086ae) (addR64R64Effect 0x1086ae 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1086ae 8 7).toInstrSpec (add_r64_r64_effect_step 0x1086ae 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x1086b1 [0x49, 0x31, 0xF0] (fun s => s.RIP = 0x1086b1) (xorR64R64Effect 0x1086b1 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1086b1 8 6).toInstrSpec (xor_r64_r64_effect_step 0x1086b1 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x1086b4 [0x4C, 0x89, 0x44, 0x24, 0x28] (StorePre 0x1086b4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1086b4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1086b4 8 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1086b4 8 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1086b4 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x1086b9 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x1086b9) (movR64R64Effect 0x1086b9 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1086b9 6 2).toInstrSpec (mov_r64_r64_effect_step 0x1086b9 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x1086bc [0x48, 0xC1, 0xEE, 0x08] (fun s => s.RIP = 0x1086bc) (shrR64Effect 0x1086bc 4 6 8)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x1086bc 4 6 8).toInstrSpec (shr_r64_imm8_effect_step 0x1086bc 0x48 0xee 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x1086c0 [0x48, 0x31, 0xD6] (fun s => s.RIP = 0x1086c0) (xorR64R64Effect 0x1086c0 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1086c0 6 2).toInstrSpec (xor_r64_r64_effect_step 0x1086c0 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x1086c3 [0x4C, 0x21, 0xF6] (fun s => s.RIP = 0x1086c3) (andR64R64Effect 0x1086c3 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1086c3 6 14).toInstrSpec (and_r64_r64_effect_step 0x1086c3 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x1086c6 [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x1086c6) (movR64R64Effect 0x1086c6 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1086c6 7 6).toInstrSpec (mov_r64_r64_effect_step 0x1086c6 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x1086c9 [0x48, 0xC1, 0xE7, 0x08] (fun s => s.RIP = 0x1086c9) (shlR64Effect 0x1086c9 4 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64Effect_footprint 0x1086c9 4 7 8).toInstrSpec (shl_r64_imm8_effect_step 0x1086c9 0x48 0xe7 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x1086cd [0x48, 0x01, 0xF7] (fun s => s.RIP = 0x1086cd) (addR64R64Effect 0x1086cd 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1086cd 7 6).toInstrSpec (add_r64_r64_effect_step 0x1086cd 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x1086d0 [0x48, 0x31, 0xD7] (fun s => s.RIP = 0x1086d0) (xorR64R64Effect 0x1086d0 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1086d0 7 2).toInstrSpec (xor_r64_r64_effect_step 0x1086d0 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x1086d3 [0x48, 0x89, 0x7C, 0x24, 0x30] (StorePre 0x1086d3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1086d3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1086d3 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1086d3 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1086d3 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f58 : InstrSpec 0x1086d8 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x1086d8) (movR64R64Effect 0x1086d8 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1086d8 2 1).toInstrSpec (mov_r64_r64_effect_step 0x1086d8 0x48 0xca (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x1086db [0x48, 0xC1, 0xEA, 0x08] (fun s => s.RIP = 0x1086db) (shrR64Effect 0x1086db 4 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x1086db 4 2 8).toInstrSpec (shr_r64_imm8_effect_step 0x1086db 0x48 0xea 0x8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f40 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 128), (8, 117), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10869d) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f41 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 130), (8, 117), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086a1) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f42 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 132), (8, 117), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086a4) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f43 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 134), (8, 117), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086a7) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f44 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 134), (8, 136), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086aa) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f45 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 134), (8, 138), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086ae) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f46 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 134), (8, 140), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086b1) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f47 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 134), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086b4) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.exec (n := 144) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 134), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086b9) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f49 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 145), (7, 134), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086bc) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f50 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 147), (7, 134), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086c0) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f51 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 149), (7, 134), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086c3) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f52 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 151), (7, 134), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086c6) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f53 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 151), (7, 153), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086c9) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f54 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 151), (7, 155), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086cd) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f55 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 151), (7, 157), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086d0) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f56 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 151), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086d3) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.exec (n := 161) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 151), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086d8) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f58 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 0), (1, 1), (2, 162), (3, 74), (4, 4), (5, 56), (6, 151), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086db) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f59 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 0), (1, 1), (2, 164), (3, 74), (4, 4), (5, 56), (6, 151), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086df) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l108600_3 code

theorem rest_l108600_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x108600 bytes_l108600) [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 83), (11, 89), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      60 0x108654 bytes_l108600_1 b_l108600_1 := by
  have f20 : InstrSpec 0x108654 [0x4D, 0x31, 0xCB] (fun s => s.RIP = 0x108654) (xorR64R64Effect 0x108654 11 9)
      [.gpr 11, .gpr 9] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108654 11 9).toInstrSpec (xor_r64_r64_effect_step 0x108654 0x4d 0xcb (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x108657 [0x4C, 0x89, 0x5C, 0x24, 0x10] (StorePre 0x108657 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108657 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108657 11 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108657 11 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x108657 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x10865c [0x4D, 0x89, 0xC1] (fun s => s.RIP = 0x10865c) (movR64R64Effect 0x10865c 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10865c 9 8).toInstrSpec (mov_r64_r64_effect_step 0x10865c 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x10865f [0x49, 0xC1, 0xE9, 0x08] (fun s => s.RIP = 0x10865f) (shrR64Effect 0x10865f 4 9 8)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x10865f 4 9 8).toInstrSpec (shr_r64_imm8_effect_step 0x10865f 0x49 0xe9 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x108663 [0x4D, 0x31, 0xC1] (fun s => s.RIP = 0x108663) (xorR64R64Effect 0x108663 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108663 9 8).toInstrSpec (xor_r64_r64_effect_step 0x108663 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x108666 [0x4D, 0x21, 0xF1] (fun s => s.RIP = 0x108666) (andR64R64Effect 0x108666 9 14)
      [.gpr 9, .gpr 14] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108666 9 14).toInstrSpec (and_r64_r64_effect_step 0x108666 0x4d 0xf1 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x108669 [0x4D, 0x89, 0xCA] (fun s => s.RIP = 0x108669) (movR64R64Effect 0x108669 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x108669 10 9).toInstrSpec (mov_r64_r64_effect_step 0x108669 0x4d 0xca (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x10866c [0x49, 0xC1, 0xE2, 0x08] (fun s => s.RIP = 0x10866c) (shlR64Effect 0x10866c 4 10 8)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR64Effect_footprint 0x10866c 4 10 8).toInstrSpec (shl_r64_imm8_effect_step 0x10866c 0x49 0xe2 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x108670 [0x4D, 0x01, 0xCA] (fun s => s.RIP = 0x108670) (addR64R64Effect 0x108670 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x108670 10 9).toInstrSpec (add_r64_r64_effect_step 0x108670 0x4d 0xca (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x108673 [0x4D, 0x31, 0xC2] (fun s => s.RIP = 0x108673) (xorR64R64Effect 0x108673 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108673 10 8).toInstrSpec (xor_r64_r64_effect_step 0x108673 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x108676 [0x4C, 0x89, 0x54, 0x24, 0x18] (StorePre 0x108676 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x108676 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108676 10 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108676 10 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x108676 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x10867b [0x49, 0x89, 0xF8] (fun s => s.RIP = 0x10867b) (movR64R64Effect 0x10867b 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10867b 8 7).toInstrSpec (mov_r64_r64_effect_step 0x10867b 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10867e [0x49, 0xC1, 0xE8, 0x08] (fun s => s.RIP = 0x10867e) (shrR64Effect 0x10867e 4 8 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x10867e 4 8 8).toInstrSpec (shr_r64_imm8_effect_step 0x10867e 0x49 0xe8 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x108682 [0x49, 0x31, 0xF8] (fun s => s.RIP = 0x108682) (xorR64R64Effect 0x108682 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108682 8 7).toInstrSpec (xor_r64_r64_effect_step 0x108682 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x108685 [0x4D, 0x21, 0xF0] (fun s => s.RIP = 0x108685) (andR64R64Effect 0x108685 8 14)
      [.gpr 8, .gpr 14] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108685 8 14).toInstrSpec (and_r64_r64_effect_step 0x108685 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x108688 [0x4D, 0x89, 0xC1] (fun s => s.RIP = 0x108688) (movR64R64Effect 0x108688 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x108688 9 8).toInstrSpec (mov_r64_r64_effect_step 0x108688 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x10868b [0x49, 0xC1, 0xE1, 0x08] (fun s => s.RIP = 0x10868b) (shlR64Effect 0x10868b 4 9 8)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR64Effect_footprint 0x10868b 4 9 8).toInstrSpec (shl_r64_imm8_effect_step 0x10868b 0x49 0xe1 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x10868f [0x4D, 0x01, 0xC1] (fun s => s.RIP = 0x10868f) (addR64R64Effect 0x10868f 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10868f 9 8).toInstrSpec (add_r64_r64_effect_step 0x10868f 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x108692 [0x49, 0x31, 0xF9] (fun s => s.RIP = 0x108692) (xorR64R64Effect 0x108692 9 7)
      [.gpr 9, .gpr 7] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108692 9 7).toInstrSpec (xor_r64_r64_effect_step 0x108692 0x49 0xf9 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x108695 [0x4C, 0x89, 0x4C, 0x24, 0x20] (StorePre 0x108695 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x108695 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108695 9 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108695 9 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x108695 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 83), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108657) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 83), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10865c) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f22 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 94), (10, 83), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10865f) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f23 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 96), (10, 83), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108663) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f24 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 98), (10, 83), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108666) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f25 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 100), (10, 83), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108669) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f26 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 100), (10, 102), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10866c) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f27 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 100), (10, 104), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108670) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f28 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 100), (10, 106), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108673) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f29 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 100), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108676) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.exec (n := 110) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 100), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10867b) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f31 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 111), (9, 100), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10867e) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f32 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 113), (9, 100), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108682) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f33 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 115), (9, 100), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108685) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f34 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 117), (9, 100), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108688) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f35 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 117), (9, 119), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10868b) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 117), (9, 121), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10868f) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 117), (9, 123), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108692) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f38 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 117), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108695) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.exec (n := 127) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 117), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10869a) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l108600_2 code

theorem rest_l108600 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108600 bytes_l108600) (entryMap (live .l108600))
      80 0x108600 bytes_l108600 b_l108600 := by
  have f0 : InstrSpec 0x108600 [0x48, 0x8B, 0xAC, 0x24, 0xE0, 0x00, 0x00, 0x00] (LoadPre 0x108600 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x108600 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108600 5 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x108600 5 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_r64_m64_effect_step 0x108600 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x108608 [0x48, 0x89, 0xAC, 0x24, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x108608 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x108608 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108608 5 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108608 5 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x108608 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x108610 [0x48, 0xC1, 0xE5, 0x06] (fun s => s.RIP = 0x108610) (shlR64Effect 0x108610 4 5 6)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shlR64Effect_footprint 0x108610 4 5 6).toInstrSpec (shl_r64_imm8_effect_step 0x108610 0x48 0xe5 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x108614 [0x4D, 0x89, 0xD3] (fun s => s.RIP = 0x108614) (movR64R64Effect 0x108614 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x108614 11 10).toInstrSpec (mov_r64_r64_effect_step 0x108614 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x108617 [0x49, 0xC1, 0xEB, 0x08] (fun s => s.RIP = 0x108617) (shrR64Effect 0x108617 4 11 8)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR64Effect_footprint 0x108617 4 11 8).toInstrSpec (shr_r64_imm8_effect_step 0x108617 0x49 0xeb 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10861b [0x4D, 0x31, 0xD3] (fun s => s.RIP = 0x10861b) (xorR64R64Effect 0x10861b 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10861b 11 10).toInstrSpec (xor_r64_r64_effect_step 0x10861b 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10861e [0x49, 0xBE, 0x00, 0x00, 0xFF, 0x00, 0x00, 0x00, 0xFF, 0x00] (fun s => s.RIP = 0x10861e) (movR64Imm64Effect 0x10861e 14 0xff000000ff0000)
      [] [] [.reg 14, .rip] :=
    (movR64Imm64Effect_footprint 0x10861e 14 0xff000000ff0000).toInstrSpec (mov_r64_imm64_effect_step 0x10861e 0x49 0xbe (by decide) (by decide) 0xff000000ff0000) pre_rip
  have f7 : InstrSpec 0x108628 [0x4D, 0x21, 0xF3] (fun s => s.RIP = 0x108628) (andR64R64Effect 0x108628 11 14)
      [.gpr 11, .gpr 14] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108628 11 14).toInstrSpec (and_r64_r64_effect_step 0x108628 0x4d 0xf3 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10862b [0x4C, 0x89, 0xDB] (fun s => s.RIP = 0x10862b) (movR64R64Effect 0x10862b 3 11)
      [.gpr 11] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10862b 3 11).toInstrSpec (mov_r64_r64_effect_step 0x10862b 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10862e [0x48, 0xC1, 0xE3, 0x08] (fun s => s.RIP = 0x10862e) (shlR64Effect 0x10862e 4 3 8)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shlR64Effect_footprint 0x10862e 4 3 8).toInstrSpec (shl_r64_imm8_effect_step 0x10862e 0x48 0xe3 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x108632 [0x4C, 0x01, 0xDB] (fun s => s.RIP = 0x108632) (addR64R64Effect 0x108632 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x108632 3 11).toInstrSpec (add_r64_r64_effect_step 0x108632 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x108635 [0x4C, 0x31, 0xD3] (fun s => s.RIP = 0x108635) (xorR64R64Effect 0x108635 3 10)
      [.gpr 3, .gpr 10] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108635 3 10).toInstrSpec (xor_r64_r64_effect_step 0x108635 0x4c 0xd3 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x108638 [0x48, 0x89, 0x5C, 0x24, 0x08] (StorePre 0x108638 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108638 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108638 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108638 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x108638 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x10863d [0x4D, 0x89, 0xCA] (fun s => s.RIP = 0x10863d) (movR64R64Effect 0x10863d 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10863d 10 9).toInstrSpec (mov_r64_r64_effect_step 0x10863d 0x4d 0xca (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x108640 [0x49, 0xC1, 0xEA, 0x08] (fun s => s.RIP = 0x108640) (shrR64Effect 0x108640 4 10 8)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR64Effect_footprint 0x108640 4 10 8).toInstrSpec (shr_r64_imm8_effect_step 0x108640 0x49 0xea 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x108644 [0x4D, 0x31, 0xCA] (fun s => s.RIP = 0x108644) (xorR64R64Effect 0x108644 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108644 10 9).toInstrSpec (xor_r64_r64_effect_step 0x108644 0x4d 0xca (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x108647 [0x4D, 0x21, 0xF2] (fun s => s.RIP = 0x108647) (andR64R64Effect 0x108647 10 14)
      [.gpr 10, .gpr 14] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108647 10 14).toInstrSpec (and_r64_r64_effect_step 0x108647 0x4d 0xf2 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10864a [0x4D, 0x89, 0xD3] (fun s => s.RIP = 0x10864a) (movR64R64Effect 0x10864a 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10864a 11 10).toInstrSpec (mov_r64_r64_effect_step 0x10864a 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10864d [0x49, 0xC1, 0xE3, 0x08] (fun s => s.RIP = 0x10864d) (shlR64Effect 0x10864d 4 11 8)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR64Effect_footprint 0x10864d 4 11 8).toInstrSpec (shl_r64_imm8_effect_step 0x10864d 0x49 0xe3 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x108651 [0x4D, 0x01, 0xD3] (fun s => s.RIP = 0x108651) (addR64R64Effect 0x108651 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x108651 11 10).toInstrSpec (add_r64_r64_effect_step 0x108651 0x4d 0xd3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108608) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108610) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108614) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 58), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108617) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10861b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 62), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10861e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 62), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108628) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10862b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10862e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 70), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108632) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 72), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108635) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108638) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10863d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 77), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108640) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 79), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108644) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 81), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108647) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 83), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10864a) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 83), (11, 85), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10864d) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 83), (11, 87), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108651) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 83), (11, 89), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108654) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l108600_1 code

theorem block_l108600 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108600 :=
  Rest.liftedBlock (rest_l108600 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108600 x hx)

theorem rest_l108728 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108728 bytes_l108728) (entryMap (live .l108728))
      20 0x108728 bytes_l108728 b_l108728 := by
  have f0 : InstrSpec 0x108728 [0x48, 0x8B, 0x84, 0x24, 0xD8, 0x04, 0x00, 0x00] (LoadPre 0x108728 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x4d8)) s (0x108728 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108728 0 (.sib 4 none 0 (.d32 0x4d8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108728 0 (.sib 4 none 0 (.d32 0x4d8))).toInstrSpec (mov_r64_m64_effect_step 0x108728 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x4d8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x108730 [0x48, 0x31, 0x44, 0x24, 0x08] (StorePre 0x108730 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108730 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108730 5 64 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x108730 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (xor_m64_r64_effect_step 0x108730 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x108735 [0x48, 0x8B, 0x84, 0x24, 0xE0, 0x04, 0x00, 0x00] (LoadPre 0x108735 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x4e0)) s (0x108735 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108735 0 (.sib 4 none 0 (.d32 0x4e0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108735 0 (.sib 4 none 0 (.d32 0x4e0))).toInstrSpec (mov_r64_m64_effect_step 0x108735 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x4e0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10873d [0x48, 0x31, 0x44, 0x24, 0x10] (StorePre 0x10873d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10873d + BitVec.ofNat 64 5)) 8) (xorMREffect 0x10873d 5 64 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x10873d 5 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (xor_m64_r64_effect_step 0x10873d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x108742 [0x48, 0x8B, 0x84, 0x24, 0xE8, 0x04, 0x00, 0x00] (LoadPre 0x108742 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x4e8)) s (0x108742 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108742 0 (.sib 4 none 0 (.d32 0x4e8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108742 0 (.sib 4 none 0 (.d32 0x4e8))).toInstrSpec (mov_r64_m64_effect_step 0x108742 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x4e8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10874a [0x48, 0x31, 0x44, 0x24, 0x18] (StorePre 0x10874a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10874a + BitVec.ofNat 64 5)) 8) (xorMREffect 0x10874a 5 64 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x10874a 5 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (xor_m64_r64_effect_step 0x10874a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10874f [0x48, 0x8B, 0x84, 0x24, 0xF0, 0x04, 0x00, 0x00] (LoadPre 0x10874f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x4f0)) s (0x10874f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10874f 0 (.sib 4 none 0 (.d32 0x4f0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10874f 0 (.sib 4 none 0 (.d32 0x4f0))).toInstrSpec (mov_r64_m64_effect_step 0x10874f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x4f0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x108757 [0x48, 0x31, 0x44, 0x24, 0x20] (StorePre 0x108757 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x108757 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108757 5 64 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x108757 5 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (xor_m64_r64_effect_step 0x108757 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10875c [0x48, 0x8B, 0x84, 0x24, 0xF8, 0x04, 0x00, 0x00] (LoadPre 0x10875c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x4f8)) s (0x10875c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10875c 0 (.sib 4 none 0 (.d32 0x4f8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10875c 0 (.sib 4 none 0 (.d32 0x4f8))).toInstrSpec (mov_r64_m64_effect_step 0x10875c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x4f8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x108764 [0x48, 0x31, 0x44, 0x24, 0x28] (StorePre 0x108764 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x108764 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108764 5 64 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x108764 5 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (xor_m64_r64_effect_step 0x108764 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x108769 [0x48, 0x8B, 0x84, 0x24, 0x00, 0x05, 0x00, 0x00] (LoadPre 0x108769 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x500)) s (0x108769 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108769 0 (.sib 4 none 0 (.d32 0x500)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108769 0 (.sib 4 none 0 (.d32 0x500))).toInstrSpec (mov_r64_m64_effect_step 0x108769 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x500)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x108771 [0x48, 0x31, 0x44, 0x24, 0x30] (StorePre 0x108771 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108771 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108771 5 64 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x108771 5 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (xor_m64_r64_effect_step 0x108771 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x108776 [0x48, 0x8B, 0x84, 0x24, 0x08, 0x05, 0x00, 0x00] (LoadPre 0x108776 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x508)) s (0x108776 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108776 0 (.sib 4 none 0 (.d32 0x508)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108776 0 (.sib 4 none 0 (.d32 0x508))).toInstrSpec (mov_r64_m64_effect_step 0x108776 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x508)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10877e [0x48, 0x31, 0x44, 0x24, 0x38] (StorePre 0x10877e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10877e + BitVec.ofNat 64 5)) 8) (xorMREffect 0x10877e 5 64 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x10877e 5 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (xor_m64_r64_effect_step 0x10877e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x108783 [0x48, 0x8B, 0x84, 0x24, 0x10, 0x05, 0x00, 0x00] (LoadPre 0x108783 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x510)) s (0x108783 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108783 0 (.sib 4 none 0 (.d32 0x510)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108783 0 (.sib 4 none 0 (.d32 0x510))).toInstrSpec (mov_r64_m64_effect_step 0x108783 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x510)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x10878b [0x48, 0x31, 0x44, 0x24, 0x40] (StorePre 0x10878b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10878b + BitVec.ofNat 64 5)) 8) (xorMREffect 0x10878b 5 64 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x10878b 5 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (xor_m64_r64_effect_step 0x10878b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x108790 [0xBA, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108790) (movR32Imm32Effect 0x108790 5 2 0x8)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x108790 5 2 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x108790 0xba (by decide) 0x8) pre_rip
  have f17 : InstrSpec 0x108795 [0x48, 0x8D, 0xBC, 0x24, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108795) (leaR64Effect 0x108795 7 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x108795 7 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (lea_r64_effect_step 0x108795 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10879d [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x10879d) (movR64R64Effect 0x10879d 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10879d 6 3).toInstrSpec (mov_r64_r64_effect_step 0x10879d 0x48 0xde (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1087a0 [0xE8, 0x6B, 0x1A, 0x00, 0x00] (PushPre 0x1087a0 5) (callEffect (fun _ => 0x10a210) 0x1087a5)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1087a0 0x10a210 0x1087a5).toInstrSpec (call_rel32_effect_step 0x1087a0 0x1a6b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108730) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108735) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10873d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108742) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10874a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10874f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108757) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10875c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108764) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108769) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108771) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108776) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10877e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108783) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10878b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108790) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 74), (2, 77), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108795) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 74), (2, 77), (3, 3), (4, 4), (5, 5), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10879d) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 74), (2, 77), (3, 3), (4, 4), (5, 5), (6, 81), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087a0) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 74), (2, 77), (3, 3), (4, 83), (5, 5), (6, 81), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a210) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem block_l108728 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108728 :=
  Rest.liftedBlock (rest_l108728 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108728 x hx)

theorem rest_l1087a5_15 [Bindings] (code : CodeMap) :
    Rest (n := 539) code lifted (codeRange 0x1087a5 bytes_l1087a5) [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]
      13 0x108e50 bytes_l1087a5_15 b_l1087a5_15 := by
  have f300 : InstrSpec 0x108e50 [0x44, 0x88, 0x4C, 0x28, 0x3A] (StorePre 0x108e50 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3a)) s (0x108e50 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e50 5 9 (.sib 0 (some 5) 0 (.d8 0x3a)))
      [.gpr 9, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108e50 5 9 (.sib 0 (some 5) 0 (.d8 0x3a))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108e50 0x44 (by decide) 1 (.sib 0 (some 5) 0 (.d8 0x3a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f301 : InstrSpec 0x108e55 [0x44, 0x88, 0x44, 0x28, 0x3B] (StorePre 0x108e55 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3b)) s (0x108e55 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e55 5 8 (.sib 0 (some 5) 0 (.d8 0x3b)))
      [.gpr 8, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108e55 5 8 (.sib 0 (some 5) 0 (.d8 0x3b))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108e55 0x44 (by decide) 0 (.sib 0 (some 5) 0 (.d8 0x3b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f302 : InstrSpec 0x108e5a [0x40, 0x88, 0x7C, 0x28, 0x3C] (StorePre 0x108e5a 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3c)) s (0x108e5a + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e5a 5 7 (.sib 0 (some 5) 0 (.d8 0x3c)))
      [.gpr 7, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108e5a 5 7 (.sib 0 (some 5) 0 (.d8 0x3c))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108e5a 0x40 (by decide) 7 (.sib 0 (some 5) 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f303 : InstrSpec 0x108e5f [0x40, 0x88, 0x74, 0x28, 0x3D] (StorePre 0x108e5f 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3d)) s (0x108e5f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e5f 5 6 (.sib 0 (some 5) 0 (.d8 0x3d)))
      [.gpr 6, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108e5f 5 6 (.sib 0 (some 5) 0 (.d8 0x3d))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108e5f 0x40 (by decide) 6 (.sib 0 (some 5) 0 (.d8 0x3d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f304 : InstrSpec 0x108e64 [0x88, 0x54, 0x28, 0x3E] (StorePre 0x108e64 4 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3e)) s (0x108e64 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108e64 4 2 (.sib 0 (some 5) 0 (.d8 0x3e)))
      [.gpr 2, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108e64 4 2 (.sib 0 (some 5) 0 (.d8 0x3e))).toInstrSpec (mov_m8_r8_effect_step 0x108e64 2 (by decide) (.sib 0 (some 5) 0 (.d8 0x3e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f305 : InstrSpec 0x108e68 [0x48, 0x89, 0xC2] (fun s => s.RIP = 0x108e68) (movR64R64Effect 0x108e68 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x108e68 2 0).toInstrSpec (mov_r64_r64_effect_step 0x108e68 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f306 : InstrSpec 0x108e6b [0x88, 0x4C, 0x28, 0x3F] (StorePre 0x108e6b 4 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3f)) s (0x108e6b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108e6b 4 1 (.sib 0 (some 5) 0 (.d8 0x3f)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108e6b 4 1 (.sib 0 (some 5) 0 (.d8 0x3f))).toInstrSpec (mov_m8_r8_effect_step 0x108e6b 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x3f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f307 : InstrSpec 0x108e6f [0x48, 0x8B, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00] (LoadPre 0x108e6f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x108e6f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108e6f 1 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x108e6f 1 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_r64_m64_effect_step 0x108e6f 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f308 : InstrSpec 0x108e77 [0x48, 0xFF, 0xC1] (fun s => s.RIP = 0x108e77) (incR64Effect 0x108e77 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (incR64Effect_footprint 0x108e77 1).toInstrSpec (inc_r64_effect_step 0x108e77 0x48 0xc1 (by decide) (by decide) (by decide)) pre_rip
  have f309 : InstrSpec 0x108e7a [0x48, 0x89, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x108e7a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x108e7a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e7a 1 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108e7a 1 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x108e7a 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f310 : InstrSpec 0x108e82 [0x48, 0x39, 0x8C, 0x24, 0x48, 0x01, 0x00, 0x00] (LoadPre 0x108e82 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x108e82 + BitVec.ofNat 64 8)) 8) (cmpMREffect 0x108e82 8 64 1 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 1, .gpr 4] [] [.flags, .rip] :=
    (cmpMREffect64_footprint 0x108e82 8 1 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (cmp_m64_r64_effect_step 0x108e82 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f311 : InstrSpec 0x108e8a [0x4C, 0x8B, 0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00] (LoadPre 0x108e8a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x108e8a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108e8a 9 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x108e8a 9 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_r64_m64_effect_step 0x108e8a 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 539) (RestInside.exec (n := 539) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e55) f300 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 540) (RestInside.exec (n := 540) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e5a) f301 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 541) (RestInside.exec (n := 541) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e5f) f302 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 542) (RestInside.exec (n := 542) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e64) f303 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 543) (RestInside.exec (n := 543) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e68) f304 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 544) (RestInside.out (n := 544) f305 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 545) (ρ' := [(0, 375), (1, 373), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e6b) f305 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 546) (RestInside.exec (n := 546) (ρ' := [(0, 375), (1, 373), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e6f) f306 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 547) (RestInside.out (n := 547) f307 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 548) (ρ' := [(0, 375), (1, 547), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e77) f307 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 549) (RestInside.out (n := 549) f308 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 550) (ρ' := [(0, 375), (1, 549), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e7a) f308 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 551) (RestInside.exec (n := 551) (ρ' := [(0, 375), (1, 549), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e82) f309 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 552) (RestInside.out (n := 552) f310 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 553) (ρ' := [(0, 375), (1, 549), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (19, 552), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e8a) f310 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 554) (RestInside.out (n := 554) f311 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 555) (ρ' := [(0, 375), (1, 549), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 554), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (19, 552), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e92) f311 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 556) (jcc_rel32_effect_step 0x108e92 4 0x671) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l1087a5_14 [Bindings] (code : CodeMap) :
    Rest (n := 512) code lifted (codeRange 0x1087a5 bytes_l1087a5) [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 509), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]
      33 0x108de6 bytes_l1087a5_14 b_l1087a5_14 := by
  have f280 : InstrSpec 0x108de6 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4E] (LoadPre 0x108de6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4e)) s (0x108de6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108de6 6 13 (.sib 4 none 0 (.d8 0x4e)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108de6 6 13 (.sib 4 none 0 (.d8 0x4e))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108de6 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x4e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f281 : InstrSpec 0x108dec [0x44, 0x88, 0x6C, 0x28, 0x2D] (StorePre 0x108dec 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2d)) s (0x108dec + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108dec 5 13 (.sib 0 (some 5) 0 (.d8 0x2d)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108dec 5 13 (.sib 0 (some 5) 0 (.d8 0x2d))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108dec 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f282 : InstrSpec 0x108df1 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4D] (LoadPre 0x108df1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x108df1 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108df1 6 13 (.sib 4 none 0 (.d8 0x4d)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108df1 6 13 (.sib 4 none 0 (.d8 0x4d))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108df1 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x4d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f283 : InstrSpec 0x108df7 [0x44, 0x88, 0x6C, 0x28, 0x2E] (StorePre 0x108df7 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2e)) s (0x108df7 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108df7 5 13 (.sib 0 (some 5) 0 (.d8 0x2e)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108df7 5 13 (.sib 0 (some 5) 0 (.d8 0x2e))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108df7 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x2e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f284 : InstrSpec 0x108dfc [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4C] (LoadPre 0x108dfc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x108dfc + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108dfc 6 13 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108dfc 6 13 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108dfc 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f285 : InstrSpec 0x108e02 [0x44, 0x88, 0x6C, 0x28, 0x2F] (StorePre 0x108e02 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2f)) s (0x108e02 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e02 5 13 (.sib 0 (some 5) 0 (.d8 0x2f)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108e02 5 13 (.sib 0 (some 5) 0 (.d8 0x2f))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108e02 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x2f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f286 : InstrSpec 0x108e07 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4B] (LoadPre 0x108e07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x108e07 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108e07 6 13 (.sib 4 none 0 (.d8 0x4b)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108e07 6 13 (.sib 4 none 0 (.d8 0x4b))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108e07 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x4b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f287 : InstrSpec 0x108e0d [0x44, 0x88, 0x6C, 0x28, 0x30] (StorePre 0x108e0d 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x30)) s (0x108e0d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e0d 5 13 (.sib 0 (some 5) 0 (.d8 0x30)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108e0d 5 13 (.sib 0 (some 5) 0 (.d8 0x30))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108e0d 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f288 : InstrSpec 0x108e12 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4A] (LoadPre 0x108e12 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x108e12 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108e12 6 13 (.sib 4 none 0 (.d8 0x4a)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108e12 6 13 (.sib 4 none 0 (.d8 0x4a))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108e12 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x4a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f289 : InstrSpec 0x108e18 [0x44, 0x88, 0x6C, 0x28, 0x31] (StorePre 0x108e18 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x31)) s (0x108e18 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e18 5 13 (.sib 0 (some 5) 0 (.d8 0x31)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108e18 5 13 (.sib 0 (some 5) 0 (.d8 0x31))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108e18 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x31)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f290 : InstrSpec 0x108e1d [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x49] (LoadPre 0x108e1d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x49)) s (0x108e1d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108e1d 6 13 (.sib 4 none 0 (.d8 0x49)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108e1d 6 13 (.sib 4 none 0 (.d8 0x49))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108e1d 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x49)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f291 : InstrSpec 0x108e23 [0x44, 0x88, 0x6C, 0x28, 0x32] (StorePre 0x108e23 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x32)) s (0x108e23 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e23 5 13 (.sib 0 (some 5) 0 (.d8 0x32)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108e23 5 13 (.sib 0 (some 5) 0 (.d8 0x32))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108e23 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x32)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f292 : InstrSpec 0x108e28 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x48] (LoadPre 0x108e28 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x108e28 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108e28 6 13 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108e28 6 13 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108e28 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f293 : InstrSpec 0x108e2e [0x44, 0x88, 0x6C, 0x28, 0x33] (StorePre 0x108e2e 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x33)) s (0x108e2e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e2e 5 13 (.sib 0 (some 5) 0 (.d8 0x33)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108e2e 5 13 (.sib 0 (some 5) 0 (.d8 0x33))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108e2e 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x33)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f294 : InstrSpec 0x108e33 [0x44, 0x88, 0x64, 0x28, 0x34] (StorePre 0x108e33 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x34)) s (0x108e33 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e33 5 12 (.sib 0 (some 5) 0 (.d8 0x34)))
      [.gpr 12, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108e33 5 12 (.sib 0 (some 5) 0 (.d8 0x34))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108e33 0x44 (by decide) 4 (.sib 0 (some 5) 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f295 : InstrSpec 0x108e38 [0x44, 0x88, 0x7C, 0x28, 0x35] (StorePre 0x108e38 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x35)) s (0x108e38 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e38 5 15 (.sib 0 (some 5) 0 (.d8 0x35)))
      [.gpr 15, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108e38 5 15 (.sib 0 (some 5) 0 (.d8 0x35))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108e38 0x44 (by decide) 7 (.sib 0 (some 5) 0 (.d8 0x35)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f296 : InstrSpec 0x108e3d [0x44, 0x88, 0x74, 0x28, 0x36] (StorePre 0x108e3d 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x36)) s (0x108e3d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e3d 5 14 (.sib 0 (some 5) 0 (.d8 0x36)))
      [.gpr 14, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108e3d 5 14 (.sib 0 (some 5) 0 (.d8 0x36))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108e3d 0x44 (by decide) 6 (.sib 0 (some 5) 0 (.d8 0x36)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f297 : InstrSpec 0x108e42 [0x88, 0x5C, 0x28, 0x37] (StorePre 0x108e42 4 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x37)) s (0x108e42 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108e42 4 3 (.sib 0 (some 5) 0 (.d8 0x37)))
      [.gpr 3, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108e42 4 3 (.sib 0 (some 5) 0 (.d8 0x37))).toInstrSpec (mov_m8_r8_effect_step 0x108e42 3 (by decide) (.sib 0 (some 5) 0 (.d8 0x37)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f298 : InstrSpec 0x108e46 [0x44, 0x88, 0x5C, 0x28, 0x38] (StorePre 0x108e46 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x38)) s (0x108e46 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e46 5 11 (.sib 0 (some 5) 0 (.d8 0x38)))
      [.gpr 11, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108e46 5 11 (.sib 0 (some 5) 0 (.d8 0x38))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108e46 0x44 (by decide) 3 (.sib 0 (some 5) 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f299 : InstrSpec 0x108e4b [0x44, 0x88, 0x54, 0x28, 0x39] (StorePre 0x108e4b 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x39)) s (0x108e4b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e4b 5 10 (.sib 0 (some 5) 0 (.d8 0x39)))
      [.gpr 10, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108e4b 5 10 (.sib 0 (some 5) 0 (.d8 0x39))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108e4b 0x44 (by decide) 2 (.sib 0 (some 5) 0 (.d8 0x39)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 512) (RestInside.out (n := 512) f280 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 513) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 512), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dec) f280 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 514) (RestInside.exec (n := 514) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 512), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108df1) f281 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 515) (RestInside.out (n := 515) f282 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 516) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 515), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108df7) f282 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 517) (RestInside.exec (n := 517) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 515), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dfc) f283 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 518) (RestInside.out (n := 518) f284 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 519) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 518), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e02) f284 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 520) (RestInside.exec (n := 520) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 518), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e07) f285 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 521) (RestInside.out (n := 521) f286 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 522) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 521), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e0d) f286 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 523) (RestInside.exec (n := 523) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 521), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e12) f287 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 524) (RestInside.out (n := 524) f288 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 525) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 524), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e18) f288 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 526) (RestInside.exec (n := 526) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 524), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e1d) f289 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 527) (RestInside.out (n := 527) f290 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 528) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 527), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e23) f290 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 529) (RestInside.exec (n := 529) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 527), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e28) f291 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 530) (RestInside.out (n := 530) f292 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 531) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e2e) f292 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 532) (RestInside.exec (n := 532) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e33) f293 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 533) (RestInside.exec (n := 533) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e38) f294 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 534) (RestInside.exec (n := 534) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e3d) f295 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 535) (RestInside.exec (n := 535) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e42) f296 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 536) (RestInside.exec (n := 536) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e46) f297 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 537) (RestInside.exec (n := 537) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e4b) f298 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 538) (RestInside.exec (n := 538) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e50) f299 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1087a5_15 code

theorem rest_l1087a5_13 [Bindings] (code : CodeMap) :
    Rest (n := 482) code lifted (codeRange 0x1087a5 bytes_l1087a5) [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 479), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]
      53 0x108d78 bytes_l1087a5_13 b_l1087a5_13 := by
  have f260 : InstrSpec 0x108d78 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x58] (LoadPre 0x108d78 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x108d78 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d78 6 13 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108d78 6 13 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108d78 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f261 : InstrSpec 0x108d7e [0x44, 0x88, 0x6C, 0x28, 0x23] (StorePre 0x108d7e 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x23)) s (0x108d7e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d7e 5 13 (.sib 0 (some 5) 0 (.d8 0x23)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d7e 5 13 (.sib 0 (some 5) 0 (.d8 0x23))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108d7e 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x23)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f262 : InstrSpec 0x108d83 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x57] (LoadPre 0x108d83 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x57)) s (0x108d83 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d83 6 13 (.sib 4 none 0 (.d8 0x57)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108d83 6 13 (.sib 4 none 0 (.d8 0x57))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108d83 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x57)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f263 : InstrSpec 0x108d89 [0x44, 0x88, 0x6C, 0x28, 0x24] (StorePre 0x108d89 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x24)) s (0x108d89 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d89 5 13 (.sib 0 (some 5) 0 (.d8 0x24)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d89 5 13 (.sib 0 (some 5) 0 (.d8 0x24))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108d89 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f264 : InstrSpec 0x108d8e [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x56] (LoadPre 0x108d8e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x56)) s (0x108d8e + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d8e 6 13 (.sib 4 none 0 (.d8 0x56)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108d8e 6 13 (.sib 4 none 0 (.d8 0x56))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108d8e 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x56)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f265 : InstrSpec 0x108d94 [0x44, 0x88, 0x6C, 0x28, 0x25] (StorePre 0x108d94 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x25)) s (0x108d94 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d94 5 13 (.sib 0 (some 5) 0 (.d8 0x25)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d94 5 13 (.sib 0 (some 5) 0 (.d8 0x25))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108d94 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f266 : InstrSpec 0x108d99 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x55] (LoadPre 0x108d99 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x55)) s (0x108d99 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d99 6 13 (.sib 4 none 0 (.d8 0x55)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108d99 6 13 (.sib 4 none 0 (.d8 0x55))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108d99 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x55)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f267 : InstrSpec 0x108d9f [0x44, 0x88, 0x6C, 0x28, 0x26] (StorePre 0x108d9f 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x26)) s (0x108d9f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d9f 5 13 (.sib 0 (some 5) 0 (.d8 0x26)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d9f 5 13 (.sib 0 (some 5) 0 (.d8 0x26))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108d9f 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x26)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f268 : InstrSpec 0x108da4 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x54] (LoadPre 0x108da4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x108da4 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108da4 6 13 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108da4 6 13 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108da4 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f269 : InstrSpec 0x108daa [0x44, 0x88, 0x6C, 0x28, 0x27] (StorePre 0x108daa 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x27)) s (0x108daa + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108daa 5 13 (.sib 0 (some 5) 0 (.d8 0x27)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108daa 5 13 (.sib 0 (some 5) 0 (.d8 0x27))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108daa 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x27)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f270 : InstrSpec 0x108daf [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x53] (LoadPre 0x108daf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x108daf + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108daf 6 13 (.sib 4 none 0 (.d8 0x53)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108daf 6 13 (.sib 4 none 0 (.d8 0x53))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108daf 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x53)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f271 : InstrSpec 0x108db5 [0x44, 0x88, 0x6C, 0x28, 0x28] (StorePre 0x108db5 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x28)) s (0x108db5 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108db5 5 13 (.sib 0 (some 5) 0 (.d8 0x28)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108db5 5 13 (.sib 0 (some 5) 0 (.d8 0x28))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108db5 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f272 : InstrSpec 0x108dba [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x52] (LoadPre 0x108dba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x52)) s (0x108dba + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108dba 6 13 (.sib 4 none 0 (.d8 0x52)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108dba 6 13 (.sib 4 none 0 (.d8 0x52))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108dba 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x52)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f273 : InstrSpec 0x108dc0 [0x44, 0x88, 0x6C, 0x28, 0x29] (StorePre 0x108dc0 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x29)) s (0x108dc0 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108dc0 5 13 (.sib 0 (some 5) 0 (.d8 0x29)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108dc0 5 13 (.sib 0 (some 5) 0 (.d8 0x29))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108dc0 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x29)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f274 : InstrSpec 0x108dc5 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x51] (LoadPre 0x108dc5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x51)) s (0x108dc5 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108dc5 6 13 (.sib 4 none 0 (.d8 0x51)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108dc5 6 13 (.sib 4 none 0 (.d8 0x51))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108dc5 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x51)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f275 : InstrSpec 0x108dcb [0x44, 0x88, 0x6C, 0x28, 0x2A] (StorePre 0x108dcb 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2a)) s (0x108dcb + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108dcb 5 13 (.sib 0 (some 5) 0 (.d8 0x2a)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108dcb 5 13 (.sib 0 (some 5) 0 (.d8 0x2a))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108dcb 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x2a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f276 : InstrSpec 0x108dd0 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x50] (LoadPre 0x108dd0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x108dd0 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108dd0 6 13 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108dd0 6 13 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108dd0 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f277 : InstrSpec 0x108dd6 [0x44, 0x88, 0x6C, 0x28, 0x2B] (StorePre 0x108dd6 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2b)) s (0x108dd6 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108dd6 5 13 (.sib 0 (some 5) 0 (.d8 0x2b)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108dd6 5 13 (.sib 0 (some 5) 0 (.d8 0x2b))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108dd6 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x2b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f278 : InstrSpec 0x108ddb [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4F] (LoadPre 0x108ddb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x108ddb + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108ddb 6 13 (.sib 4 none 0 (.d8 0x4f)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108ddb 6 13 (.sib 4 none 0 (.d8 0x4f))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108ddb 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x4f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f279 : InstrSpec 0x108de1 [0x44, 0x88, 0x6C, 0x28, 0x2C] (StorePre 0x108de1 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2c)) s (0x108de1 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108de1 5 13 (.sib 0 (some 5) 0 (.d8 0x2c)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108de1 5 13 (.sib 0 (some 5) 0 (.d8 0x2c))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108de1 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 482) (RestInside.out (n := 482) f260 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 483) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 482), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d7e) f260 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 484) (RestInside.exec (n := 484) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 482), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d83) f261 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 485) (RestInside.out (n := 485) f262 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 486) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 485), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d89) f262 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 487) (RestInside.exec (n := 487) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 485), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d8e) f263 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 488) (RestInside.out (n := 488) f264 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 489) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 488), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d94) f264 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 490) (RestInside.exec (n := 490) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 488), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d99) f265 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 491) (RestInside.out (n := 491) f266 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 492) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 491), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d9f) f266 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 493) (RestInside.exec (n := 493) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 491), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108da4) f267 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 494) (RestInside.out (n := 494) f268 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 495) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 494), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108daa) f268 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 496) (RestInside.exec (n := 496) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 494), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108daf) f269 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 497) (RestInside.out (n := 497) f270 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 498) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 497), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108db5) f270 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 499) (RestInside.exec (n := 499) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 497), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dba) f271 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 500) (RestInside.out (n := 500) f272 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 501) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 500), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dc0) f272 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 502) (RestInside.exec (n := 502) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 500), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dc5) f273 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 503) (RestInside.out (n := 503) f274 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 504) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 503), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dcb) f274 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 505) (RestInside.exec (n := 505) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 503), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dd0) f275 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 506) (RestInside.out (n := 506) f276 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 507) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 506), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dd6) f276 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 508) (RestInside.exec (n := 508) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 506), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ddb) f277 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 509) (RestInside.out (n := 509) f278 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 510) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 509), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108de1) f278 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 511) (RestInside.exec (n := 511) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 509), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108de6) f279 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1087a5_14 code

theorem rest_l1087a5_12 [Bindings] (code : CodeMap) :
    Rest (n := 452) code lifted (codeRange 0x1087a5 bytes_l1087a5) [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 449), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]
      73 0x108d0a bytes_l1087a5_12 b_l1087a5_12 := by
  have f240 : InstrSpec 0x108d0a [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x62] (LoadPre 0x108d0a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x108d0a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d0a 6 13 (.sib 4 none 0 (.d8 0x62)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108d0a 6 13 (.sib 4 none 0 (.d8 0x62))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108d0a 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x62)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f241 : InstrSpec 0x108d10 [0x44, 0x88, 0x6C, 0x28, 0x19] (StorePre 0x108d10 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x19)) s (0x108d10 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d10 5 13 (.sib 0 (some 5) 0 (.d8 0x19)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d10 5 13 (.sib 0 (some 5) 0 (.d8 0x19))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108d10 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f242 : InstrSpec 0x108d15 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x61] (LoadPre 0x108d15 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x61)) s (0x108d15 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d15 6 13 (.sib 4 none 0 (.d8 0x61)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108d15 6 13 (.sib 4 none 0 (.d8 0x61))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108d15 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x61)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f243 : InstrSpec 0x108d1b [0x44, 0x88, 0x6C, 0x28, 0x1A] (StorePre 0x108d1b 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1a)) s (0x108d1b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d1b 5 13 (.sib 0 (some 5) 0 (.d8 0x1a)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d1b 5 13 (.sib 0 (some 5) 0 (.d8 0x1a))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108d1b 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f244 : InstrSpec 0x108d20 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x60] (LoadPre 0x108d20 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x108d20 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d20 6 13 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108d20 6 13 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108d20 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f245 : InstrSpec 0x108d26 [0x44, 0x88, 0x6C, 0x28, 0x1B] (StorePre 0x108d26 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1b)) s (0x108d26 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d26 5 13 (.sib 0 (some 5) 0 (.d8 0x1b)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d26 5 13 (.sib 0 (some 5) 0 (.d8 0x1b))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108d26 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f246 : InstrSpec 0x108d2b [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5F] (LoadPre 0x108d2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5f)) s (0x108d2b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d2b 6 13 (.sib 4 none 0 (.d8 0x5f)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108d2b 6 13 (.sib 4 none 0 (.d8 0x5f))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108d2b 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x5f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f247 : InstrSpec 0x108d31 [0x44, 0x88, 0x6C, 0x28, 0x1C] (StorePre 0x108d31 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1c)) s (0x108d31 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d31 5 13 (.sib 0 (some 5) 0 (.d8 0x1c)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d31 5 13 (.sib 0 (some 5) 0 (.d8 0x1c))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108d31 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f248 : InstrSpec 0x108d36 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5E] (LoadPre 0x108d36 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x108d36 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d36 6 13 (.sib 4 none 0 (.d8 0x5e)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108d36 6 13 (.sib 4 none 0 (.d8 0x5e))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108d36 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x5e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f249 : InstrSpec 0x108d3c [0x44, 0x88, 0x6C, 0x28, 0x1D] (StorePre 0x108d3c 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1d)) s (0x108d3c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d3c 5 13 (.sib 0 (some 5) 0 (.d8 0x1d)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d3c 5 13 (.sib 0 (some 5) 0 (.d8 0x1d))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108d3c 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f250 : InstrSpec 0x108d41 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5D] (LoadPre 0x108d41 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5d)) s (0x108d41 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d41 6 13 (.sib 4 none 0 (.d8 0x5d)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108d41 6 13 (.sib 4 none 0 (.d8 0x5d))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108d41 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x5d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f251 : InstrSpec 0x108d47 [0x44, 0x88, 0x6C, 0x28, 0x1E] (StorePre 0x108d47 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1e)) s (0x108d47 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d47 5 13 (.sib 0 (some 5) 0 (.d8 0x1e)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d47 5 13 (.sib 0 (some 5) 0 (.d8 0x1e))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108d47 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f252 : InstrSpec 0x108d4c [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5C] (LoadPre 0x108d4c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x108d4c + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d4c 6 13 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108d4c 6 13 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108d4c 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f253 : InstrSpec 0x108d52 [0x44, 0x88, 0x6C, 0x28, 0x1F] (StorePre 0x108d52 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1f)) s (0x108d52 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d52 5 13 (.sib 0 (some 5) 0 (.d8 0x1f)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d52 5 13 (.sib 0 (some 5) 0 (.d8 0x1f))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108d52 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f254 : InstrSpec 0x108d57 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5B] (LoadPre 0x108d57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5b)) s (0x108d57 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d57 6 13 (.sib 4 none 0 (.d8 0x5b)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108d57 6 13 (.sib 4 none 0 (.d8 0x5b))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108d57 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x5b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f255 : InstrSpec 0x108d5d [0x44, 0x88, 0x6C, 0x28, 0x20] (StorePre 0x108d5d 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x20)) s (0x108d5d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d5d 5 13 (.sib 0 (some 5) 0 (.d8 0x20)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d5d 5 13 (.sib 0 (some 5) 0 (.d8 0x20))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108d5d 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f256 : InstrSpec 0x108d62 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5A] (LoadPre 0x108d62 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5a)) s (0x108d62 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d62 6 13 (.sib 4 none 0 (.d8 0x5a)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108d62 6 13 (.sib 4 none 0 (.d8 0x5a))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108d62 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x5a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f257 : InstrSpec 0x108d68 [0x44, 0x88, 0x6C, 0x28, 0x21] (StorePre 0x108d68 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x21)) s (0x108d68 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d68 5 13 (.sib 0 (some 5) 0 (.d8 0x21)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d68 5 13 (.sib 0 (some 5) 0 (.d8 0x21))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108d68 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x21)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f258 : InstrSpec 0x108d6d [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x59] (LoadPre 0x108d6d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x59)) s (0x108d6d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d6d 6 13 (.sib 4 none 0 (.d8 0x59)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108d6d 6 13 (.sib 4 none 0 (.d8 0x59))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108d6d 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x59)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f259 : InstrSpec 0x108d73 [0x44, 0x88, 0x6C, 0x28, 0x22] (StorePre 0x108d73 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x22)) s (0x108d73 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d73 5 13 (.sib 0 (some 5) 0 (.d8 0x22)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d73 5 13 (.sib 0 (some 5) 0 (.d8 0x22))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108d73 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x22)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 452) (RestInside.out (n := 452) f240 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 453) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 452), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d10) f240 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 454) (RestInside.exec (n := 454) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 452), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d15) f241 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 455) (RestInside.out (n := 455) f242 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 456) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 455), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d1b) f242 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 457) (RestInside.exec (n := 457) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 455), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d20) f243 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 458) (RestInside.out (n := 458) f244 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 459) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 458), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d26) f244 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 460) (RestInside.exec (n := 460) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 458), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d2b) f245 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 461) (RestInside.out (n := 461) f246 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 462) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 461), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d31) f246 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 463) (RestInside.exec (n := 463) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 461), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d36) f247 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 464) (RestInside.out (n := 464) f248 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 465) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 464), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d3c) f248 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 466) (RestInside.exec (n := 466) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 464), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d41) f249 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 467) (RestInside.out (n := 467) f250 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 468) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 467), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d47) f250 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 469) (RestInside.exec (n := 469) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 467), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d4c) f251 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 470) (RestInside.out (n := 470) f252 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 471) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 470), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d52) f252 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 472) (RestInside.exec (n := 472) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 470), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d57) f253 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 473) (RestInside.out (n := 473) f254 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 474) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 473), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d5d) f254 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 475) (RestInside.exec (n := 475) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 473), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d62) f255 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 476) (RestInside.out (n := 476) f256 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 477) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 476), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d68) f256 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 478) (RestInside.exec (n := 478) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 476), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d6d) f257 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 479) (RestInside.out (n := 479) f258 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 480) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 479), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d73) f258 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 481) (RestInside.exec (n := 481) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 479), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d78) f259 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1087a5_13 code

theorem rest_l1087a5_11 [Bindings] (code : CodeMap) :
    Rest (n := 422) code lifted (codeRange 0x1087a5 bytes_l1087a5) [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 419), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]
      93 0x108c96 bytes_l1087a5_11 b_l1087a5_11 := by
  have f220 : InstrSpec 0x108c96 [0x44, 0x0F, 0xB6, 0xAC, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x108c96 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x108c96 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108c96 9 13 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108c96 9 13 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108c96 0x44 (by decide) 5 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f221 : InstrSpec 0x108c9f [0x44, 0x88, 0x6C, 0x28, 0x0F] (StorePre 0x108c9f 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xf)) s (0x108c9f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c9f 5 13 (.sib 0 (some 5) 0 (.d8 0xf)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108c9f 5 13 (.sib 0 (some 5) 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108c9f 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f222 : InstrSpec 0x108ca4 [0x44, 0x0F, 0xB6, 0xAC, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x108ca4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x108ca4 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108ca4 9 13 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108ca4 9 13 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108ca4 0x44 (by decide) 5 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f223 : InstrSpec 0x108cad [0x44, 0x88, 0x6C, 0x28, 0x10] (StorePre 0x108cad 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x10)) s (0x108cad + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108cad 5 13 (.sib 0 (some 5) 0 (.d8 0x10)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108cad 5 13 (.sib 0 (some 5) 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108cad 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f224 : InstrSpec 0x108cb2 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6A] (LoadPre 0x108cb2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6a)) s (0x108cb2 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108cb2 6 13 (.sib 4 none 0 (.d8 0x6a)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108cb2 6 13 (.sib 4 none 0 (.d8 0x6a))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108cb2 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x6a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f225 : InstrSpec 0x108cb8 [0x44, 0x88, 0x6C, 0x28, 0x11] (StorePre 0x108cb8 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x11)) s (0x108cb8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108cb8 5 13 (.sib 0 (some 5) 0 (.d8 0x11)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108cb8 5 13 (.sib 0 (some 5) 0 (.d8 0x11))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108cb8 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f226 : InstrSpec 0x108cbd [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x69] (LoadPre 0x108cbd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x69)) s (0x108cbd + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108cbd 6 13 (.sib 4 none 0 (.d8 0x69)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108cbd 6 13 (.sib 4 none 0 (.d8 0x69))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108cbd 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x69)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f227 : InstrSpec 0x108cc3 [0x44, 0x88, 0x6C, 0x28, 0x12] (StorePre 0x108cc3 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x12)) s (0x108cc3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108cc3 5 13 (.sib 0 (some 5) 0 (.d8 0x12)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108cc3 5 13 (.sib 0 (some 5) 0 (.d8 0x12))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108cc3 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f228 : InstrSpec 0x108cc8 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x68] (LoadPre 0x108cc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x108cc8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108cc8 6 13 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108cc8 6 13 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108cc8 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f229 : InstrSpec 0x108cce [0x44, 0x88, 0x6C, 0x28, 0x13] (StorePre 0x108cce 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x13)) s (0x108cce + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108cce 5 13 (.sib 0 (some 5) 0 (.d8 0x13)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108cce 5 13 (.sib 0 (some 5) 0 (.d8 0x13))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108cce 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f230 : InstrSpec 0x108cd3 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x67] (LoadPre 0x108cd3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x67)) s (0x108cd3 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108cd3 6 13 (.sib 4 none 0 (.d8 0x67)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108cd3 6 13 (.sib 4 none 0 (.d8 0x67))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108cd3 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x67)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f231 : InstrSpec 0x108cd9 [0x44, 0x88, 0x6C, 0x28, 0x14] (StorePre 0x108cd9 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x14)) s (0x108cd9 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108cd9 5 13 (.sib 0 (some 5) 0 (.d8 0x14)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108cd9 5 13 (.sib 0 (some 5) 0 (.d8 0x14))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108cd9 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f232 : InstrSpec 0x108cde [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x66] (LoadPre 0x108cde (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x108cde + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108cde 6 13 (.sib 4 none 0 (.d8 0x66)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108cde 6 13 (.sib 4 none 0 (.d8 0x66))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108cde 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x66)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f233 : InstrSpec 0x108ce4 [0x44, 0x88, 0x6C, 0x28, 0x15] (StorePre 0x108ce4 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x15)) s (0x108ce4 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108ce4 5 13 (.sib 0 (some 5) 0 (.d8 0x15)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108ce4 5 13 (.sib 0 (some 5) 0 (.d8 0x15))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108ce4 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f234 : InstrSpec 0x108ce9 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x65] (LoadPre 0x108ce9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x65)) s (0x108ce9 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108ce9 6 13 (.sib 4 none 0 (.d8 0x65)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108ce9 6 13 (.sib 4 none 0 (.d8 0x65))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108ce9 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x65)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f235 : InstrSpec 0x108cef [0x44, 0x88, 0x6C, 0x28, 0x16] (StorePre 0x108cef 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x16)) s (0x108cef + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108cef 5 13 (.sib 0 (some 5) 0 (.d8 0x16)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108cef 5 13 (.sib 0 (some 5) 0 (.d8 0x16))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108cef 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f236 : InstrSpec 0x108cf4 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x64] (LoadPre 0x108cf4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x108cf4 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108cf4 6 13 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108cf4 6 13 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108cf4 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f237 : InstrSpec 0x108cfa [0x44, 0x88, 0x6C, 0x28, 0x17] (StorePre 0x108cfa 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x17)) s (0x108cfa + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108cfa 5 13 (.sib 0 (some 5) 0 (.d8 0x17)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108cfa 5 13 (.sib 0 (some 5) 0 (.d8 0x17))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108cfa 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x17)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f238 : InstrSpec 0x108cff [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x63] (LoadPre 0x108cff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x63)) s (0x108cff + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108cff 6 13 (.sib 4 none 0 (.d8 0x63)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108cff 6 13 (.sib 4 none 0 (.d8 0x63))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108cff 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x63)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f239 : InstrSpec 0x108d05 [0x44, 0x88, 0x6C, 0x28, 0x18] (StorePre 0x108d05 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x18)) s (0x108d05 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d05 5 13 (.sib 0 (some 5) 0 (.d8 0x18)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d05 5 13 (.sib 0 (some 5) 0 (.d8 0x18))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108d05 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 422) (RestInside.out (n := 422) f220 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 423) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 422), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c9f) f220 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 424) (RestInside.exec (n := 424) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 422), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ca4) f221 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 425) (RestInside.out (n := 425) f222 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 426) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 425), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cad) f222 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 427) (RestInside.exec (n := 427) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 425), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cb2) f223 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 428) (RestInside.out (n := 428) f224 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 429) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 428), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cb8) f224 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 430) (RestInside.exec (n := 430) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 428), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cbd) f225 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 431) (RestInside.out (n := 431) f226 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 432) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 431), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cc3) f226 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 433) (RestInside.exec (n := 433) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 431), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cc8) f227 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 434) (RestInside.out (n := 434) f228 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 435) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 434), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cce) f228 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 436) (RestInside.exec (n := 436) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 434), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cd3) f229 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 437) (RestInside.out (n := 437) f230 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 438) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 437), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cd9) f230 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 439) (RestInside.exec (n := 439) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 437), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cde) f231 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 440) (RestInside.out (n := 440) f232 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 441) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 440), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ce4) f232 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 442) (RestInside.exec (n := 442) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 440), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ce9) f233 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 443) (RestInside.out (n := 443) f234 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 444) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 443), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cef) f234 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 445) (RestInside.exec (n := 445) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 443), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cf4) f235 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 446) (RestInside.out (n := 446) f236 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 447) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 446), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cfa) f236 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 448) (RestInside.exec (n := 448) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 446), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cff) f237 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 449) (RestInside.out (n := 449) f238 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 450) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 449), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d05) f238 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 451) (RestInside.exec (n := 451) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 449), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d0a) f239 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1087a5_12 code

theorem rest_l1087a5_10 [Bindings] (code : CodeMap) :
    Rest (n := 392) code lifted (codeRange 0x1087a5 bytes_l1087a5) [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 389), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]
      113 0x108c25 bytes_l1087a5_10 b_l1087a5_10 := by
  have f200 : InstrSpec 0x108c25 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x72] (LoadPre 0x108c25 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x108c25 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c25 6 13 (.sib 4 none 0 (.d8 0x72)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108c25 6 13 (.sib 4 none 0 (.d8 0x72))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108c25 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x72)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f201 : InstrSpec 0x108c2b [0x44, 0x88, 0x6C, 0x28, 0x05] (StorePre 0x108c2b 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x5)) s (0x108c2b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c2b 5 13 (.sib 0 (some 5) 0 (.d8 0x5)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108c2b 5 13 (.sib 0 (some 5) 0 (.d8 0x5))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108c2b 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f202 : InstrSpec 0x108c30 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x71] (LoadPre 0x108c30 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x71)) s (0x108c30 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c30 6 13 (.sib 4 none 0 (.d8 0x71)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108c30 6 13 (.sib 4 none 0 (.d8 0x71))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108c30 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x71)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f203 : InstrSpec 0x108c36 [0x44, 0x88, 0x6C, 0x28, 0x06] (StorePre 0x108c36 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x6)) s (0x108c36 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c36 5 13 (.sib 0 (some 5) 0 (.d8 0x6)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108c36 5 13 (.sib 0 (some 5) 0 (.d8 0x6))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108c36 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f204 : InstrSpec 0x108c3b [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x70] (LoadPre 0x108c3b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x108c3b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c3b 6 13 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108c3b 6 13 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108c3b 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f205 : InstrSpec 0x108c41 [0x44, 0x88, 0x6C, 0x28, 0x07] (StorePre 0x108c41 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x7)) s (0x108c41 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c41 5 13 (.sib 0 (some 5) 0 (.d8 0x7)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108c41 5 13 (.sib 0 (some 5) 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108c41 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f206 : InstrSpec 0x108c46 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6F] (LoadPre 0x108c46 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6f)) s (0x108c46 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c46 6 13 (.sib 4 none 0 (.d8 0x6f)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108c46 6 13 (.sib 4 none 0 (.d8 0x6f))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108c46 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x6f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f207 : InstrSpec 0x108c4c [0x44, 0x88, 0x6C, 0x28, 0x08] (StorePre 0x108c4c 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x8)) s (0x108c4c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c4c 5 13 (.sib 0 (some 5) 0 (.d8 0x8)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108c4c 5 13 (.sib 0 (some 5) 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108c4c 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f208 : InstrSpec 0x108c51 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6E] (LoadPre 0x108c51 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6e)) s (0x108c51 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c51 6 13 (.sib 4 none 0 (.d8 0x6e)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108c51 6 13 (.sib 4 none 0 (.d8 0x6e))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108c51 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x6e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f209 : InstrSpec 0x108c57 [0x44, 0x88, 0x6C, 0x28, 0x09] (StorePre 0x108c57 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x9)) s (0x108c57 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c57 5 13 (.sib 0 (some 5) 0 (.d8 0x9)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108c57 5 13 (.sib 0 (some 5) 0 (.d8 0x9))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108c57 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f210 : InstrSpec 0x108c5c [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6D] (LoadPre 0x108c5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6d)) s (0x108c5c + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c5c 6 13 (.sib 4 none 0 (.d8 0x6d)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108c5c 6 13 (.sib 4 none 0 (.d8 0x6d))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108c5c 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x6d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f211 : InstrSpec 0x108c62 [0x44, 0x88, 0x6C, 0x28, 0x0A] (StorePre 0x108c62 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xa)) s (0x108c62 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c62 5 13 (.sib 0 (some 5) 0 (.d8 0xa)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108c62 5 13 (.sib 0 (some 5) 0 (.d8 0xa))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108c62 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f212 : InstrSpec 0x108c67 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6C] (LoadPre 0x108c67 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x108c67 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c67 6 13 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108c67 6 13 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108c67 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f213 : InstrSpec 0x108c6d [0x44, 0x88, 0x6C, 0x28, 0x0B] (StorePre 0x108c6d 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xb)) s (0x108c6d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c6d 5 13 (.sib 0 (some 5) 0 (.d8 0xb)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108c6d 5 13 (.sib 0 (some 5) 0 (.d8 0xb))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108c6d 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f214 : InstrSpec 0x108c72 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6B] (LoadPre 0x108c72 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6b)) s (0x108c72 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c72 6 13 (.sib 4 none 0 (.d8 0x6b)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108c72 6 13 (.sib 4 none 0 (.d8 0x6b))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108c72 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x6b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f215 : InstrSpec 0x108c78 [0x44, 0x88, 0x6C, 0x28, 0x0C] (StorePre 0x108c78 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xc)) s (0x108c78 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c78 5 13 (.sib 0 (some 5) 0 (.d8 0xc)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108c78 5 13 (.sib 0 (some 5) 0 (.d8 0xc))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108c78 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f216 : InstrSpec 0x108c7d [0x44, 0x0F, 0xB6, 0xAC, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x108c7d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x108c7d + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108c7d 9 13 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108c7d 9 13 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108c7d 0x44 (by decide) 5 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f217 : InstrSpec 0x108c86 [0x44, 0x88, 0x6C, 0x28, 0x0D] (StorePre 0x108c86 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xd)) s (0x108c86 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c86 5 13 (.sib 0 (some 5) 0 (.d8 0xd)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108c86 5 13 (.sib 0 (some 5) 0 (.d8 0xd))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108c86 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f218 : InstrSpec 0x108c8b [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x78] (LoadPre 0x108c8b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x108c8b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c8b 6 13 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108c8b 6 13 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108c8b 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f219 : InstrSpec 0x108c91 [0x44, 0x88, 0x6C, 0x28, 0x0E] (StorePre 0x108c91 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xe)) s (0x108c91 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c91 5 13 (.sib 0 (some 5) 0 (.d8 0xe)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108c91 5 13 (.sib 0 (some 5) 0 (.d8 0xe))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108c91 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 392) (RestInside.out (n := 392) f200 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 393) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 392), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c2b) f200 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 394) (RestInside.exec (n := 394) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 392), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c30) f201 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 395) (RestInside.out (n := 395) f202 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 396) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 395), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c36) f202 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 397) (RestInside.exec (n := 397) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 395), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c3b) f203 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 398) (RestInside.out (n := 398) f204 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 399) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 398), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c41) f204 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 400) (RestInside.exec (n := 400) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 398), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c46) f205 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 401) (RestInside.out (n := 401) f206 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 402) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 401), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c4c) f206 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 403) (RestInside.exec (n := 403) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 401), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c51) f207 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 404) (RestInside.out (n := 404) f208 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 405) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 404), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c57) f208 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 406) (RestInside.exec (n := 406) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 404), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c5c) f209 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 407) (RestInside.out (n := 407) f210 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 408) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 407), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c62) f210 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 409) (RestInside.exec (n := 409) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 407), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c67) f211 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 410) (RestInside.out (n := 410) f212 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 411) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 410), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c6d) f212 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 412) (RestInside.exec (n := 412) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 410), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c72) f213 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 413) (RestInside.out (n := 413) f214 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 414) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 413), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c78) f214 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 415) (RestInside.exec (n := 415) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 413), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c7d) f215 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 416) (RestInside.out (n := 416) f216 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 417) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 416), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c86) f216 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 418) (RestInside.exec (n := 418) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 416), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c8b) f217 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 419) (RestInside.out (n := 419) f218 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 420) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 419), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c91) f218 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 421) (RestInside.exec (n := 421) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 419), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c96) f219 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1087a5_11 code

theorem rest_l1087a5_9 [Bindings] (code : CodeMap) :
    Rest (n := 357) code lifted (codeRange 0x1087a5 bytes_l1087a5) [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 355), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]
      133 0x108bb0 bytes_l1087a5_9 b_l1087a5_9 := by
  have f180 : InstrSpec 0x108bb0 [0x44, 0x32, 0x44, 0x28, 0x3B] (LoadPre 0x108bb0 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3b)) s (0x108bb0 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108bb0 5 8 (.sib 0 (some 5) 0 (.d8 0x3b)))
      [.gpr 8, .gpr 0, .gpr 5] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108bb0 5 8 (.sib 0 (some 5) 0 (.d8 0x3b))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108bb0 0x44 (by decide) 0 (.sib 0 (some 5) 0 (.d8 0x3b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f181 : InstrSpec 0x108bb5 [0x0F, 0xB6, 0xBC, 0x24, 0xD4, 0x00, 0x00, 0x00] (LoadPre 0x108bb5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd4)) s (0x108bb5 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108bb5 8 7 (.sib 4 none 0 (.d32 0xd4)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x108bb5 8 7 (.sib 4 none 0 (.d32 0xd4))).toInstrSpec (movzx_r32_m8_effect_step 0x108bb5 7 (.sib 4 none 0 (.d32 0xd4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f182 : InstrSpec 0x108bbd [0x40, 0x32, 0x7C, 0x28, 0x3C] (LoadPre 0x108bbd (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3c)) s (0x108bbd + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108bbd 5 7 (.sib 0 (some 5) 0 (.d8 0x3c)))
      [.gpr 7, .gpr 0, .gpr 5] [] [.reg 7, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108bbd 5 7 (.sib 0 (some 5) 0 (.d8 0x3c))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108bbd 0x40 (by decide) 7 (.sib 0 (some 5) 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f183 : InstrSpec 0x108bc2 [0x0F, 0xB6, 0xB4, 0x24, 0xD5, 0x00, 0x00, 0x00] (LoadPre 0x108bc2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd5)) s (0x108bc2 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108bc2 8 6 (.sib 4 none 0 (.d32 0xd5)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x108bc2 8 6 (.sib 4 none 0 (.d32 0xd5))).toInstrSpec (movzx_r32_m8_effect_step 0x108bc2 6 (.sib 4 none 0 (.d32 0xd5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f184 : InstrSpec 0x108bca [0x40, 0x32, 0x74, 0x28, 0x3D] (LoadPre 0x108bca (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3d)) s (0x108bca + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108bca 5 6 (.sib 0 (some 5) 0 (.d8 0x3d)))
      [.gpr 6, .gpr 0, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108bca 5 6 (.sib 0 (some 5) 0 (.d8 0x3d))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108bca 0x40 (by decide) 6 (.sib 0 (some 5) 0 (.d8 0x3d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f185 : InstrSpec 0x108bcf [0x0F, 0xB6, 0x94, 0x24, 0xD6, 0x00, 0x00, 0x00] (LoadPre 0x108bcf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd6)) s (0x108bcf + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108bcf 8 2 (.sib 4 none 0 (.d32 0xd6)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x108bcf 8 2 (.sib 4 none 0 (.d32 0xd6))).toInstrSpec (movzx_r32_m8_effect_step 0x108bcf 2 (.sib 4 none 0 (.d32 0xd6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f186 : InstrSpec 0x108bd7 [0x32, 0x54, 0x28, 0x3E] (LoadPre 0x108bd7 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3e)) s (0x108bd7 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108bd7 4 2 (.sib 0 (some 5) 0 (.d8 0x3e)))
      [.gpr 2, .gpr 0, .gpr 5] [] [.reg 2, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108bd7 4 2 (.sib 0 (some 5) 0 (.d8 0x3e))).toInstrSpec (xor_r8_m8_effect_step 0x108bd7 2 (by decide) (.sib 0 (some 5) 0 (.d8 0x3e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f187 : InstrSpec 0x108bdb [0x0F, 0xB6, 0x8C, 0x24, 0xD7, 0x00, 0x00, 0x00] (LoadPre 0x108bdb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd7)) s (0x108bdb + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108bdb 8 1 (.sib 4 none 0 (.d32 0xd7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108bdb 8 1 (.sib 4 none 0 (.d32 0xd7))).toInstrSpec (movzx_r32_m8_effect_step 0x108bdb 1 (.sib 4 none 0 (.d32 0xd7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f188 : InstrSpec 0x108be3 [0x32, 0x4C, 0x28, 0x3F] (LoadPre 0x108be3 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3f)) s (0x108be3 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108be3 4 1 (.sib 0 (some 5) 0 (.d8 0x3f)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108be3 4 1 (.sib 0 (some 5) 0 (.d8 0x3f))).toInstrSpec (xor_r8_m8_effect_step 0x108be3 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x3f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f189 : InstrSpec 0x108be7 [0x48, 0x8B, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x108be7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x108be7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108be7 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108be7 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x108be7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f190 : InstrSpec 0x108bef [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x77] (LoadPre 0x108bef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x77)) s (0x108bef + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108bef 6 13 (.sib 4 none 0 (.d8 0x77)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108bef 6 13 (.sib 4 none 0 (.d8 0x77))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108bef 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x77)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f191 : InstrSpec 0x108bf5 [0x44, 0x88, 0x2C, 0x28] (StorePre 0x108bf5 4 (fun s => AddrMode.addr (.sib 0 (some 5) 0 .none) s (0x108bf5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108bf5 4 13 (.sib 0 (some 5) 0 .none))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108bf5 4 13 (.sib 0 (some 5) 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x108bf5 0x44 (by decide) 5 (.sib 0 (some 5) 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f192 : InstrSpec 0x108bf9 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x76] (LoadPre 0x108bf9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x108bf9 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108bf9 6 13 (.sib 4 none 0 (.d8 0x76)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108bf9 6 13 (.sib 4 none 0 (.d8 0x76))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108bf9 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x76)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f193 : InstrSpec 0x108bff [0x44, 0x88, 0x6C, 0x28, 0x01] (StorePre 0x108bff 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1)) s (0x108bff + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108bff 5 13 (.sib 0 (some 5) 0 (.d8 0x1)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108bff 5 13 (.sib 0 (some 5) 0 (.d8 0x1))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108bff 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x1)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f194 : InstrSpec 0x108c04 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x75] (LoadPre 0x108c04 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x75)) s (0x108c04 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c04 6 13 (.sib 4 none 0 (.d8 0x75)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108c04 6 13 (.sib 4 none 0 (.d8 0x75))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108c04 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x75)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f195 : InstrSpec 0x108c0a [0x44, 0x88, 0x6C, 0x28, 0x02] (StorePre 0x108c0a 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2)) s (0x108c0a + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c0a 5 13 (.sib 0 (some 5) 0 (.d8 0x2)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108c0a 5 13 (.sib 0 (some 5) 0 (.d8 0x2))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108c0a 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f196 : InstrSpec 0x108c0f [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x74] (LoadPre 0x108c0f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x108c0f + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c0f 6 13 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108c0f 6 13 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108c0f 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f197 : InstrSpec 0x108c15 [0x44, 0x88, 0x6C, 0x28, 0x03] (StorePre 0x108c15 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3)) s (0x108c15 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c15 5 13 (.sib 0 (some 5) 0 (.d8 0x3)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108c15 5 13 (.sib 0 (some 5) 0 (.d8 0x3))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108c15 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f198 : InstrSpec 0x108c1a [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x73] (LoadPre 0x108c1a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x73)) s (0x108c1a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c1a 6 13 (.sib 4 none 0 (.d8 0x73)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108c1a 6 13 (.sib 4 none 0 (.d8 0x73))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108c1a 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x73)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f199 : InstrSpec 0x108c20 [0x44, 0x88, 0x6C, 0x28, 0x04] (StorePre 0x108c20 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x4)) s (0x108c20 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c20 5 13 (.sib 0 (some 5) 0 (.d8 0x4)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x108c20 5 13 (.sib 0 (some 5) 0 (.d8 0x4))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108c20 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 357) (RestInside.out (n := 357) f180 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 358) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bb5) f180 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 359) (RestInside.out (n := 359) f181 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 360) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 359), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bbd) f181 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 361) (RestInside.out (n := 361) f182 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 362) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bc2) f182 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 363) (RestInside.out (n := 363) f183 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 364) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 363), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bca) f183 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 365) (RestInside.out (n := 365) f184 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 366) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bcf) f184 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 367) (RestInside.out (n := 367) f185 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 368) (ρ' := [(0, 91), (1, 324), (2, 367), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bd7) f185 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 369) (RestInside.out (n := 369) f186 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 370) (ρ' := [(0, 91), (1, 324), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bdb) f186 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 371) (RestInside.out (n := 371) f187 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 372) (ρ' := [(0, 91), (1, 371), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108be3) f187 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 373) (RestInside.out (n := 373) f188 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 374) (ρ' := [(0, 91), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108be7) f188 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 375) (RestInside.out (n := 375) f189 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 376) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bef) f189 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 377) (RestInside.out (n := 377) f190 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 378) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 377), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bf5) f190 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 379) (RestInside.exec (n := 379) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 377), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bf9) f191 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 380) (RestInside.out (n := 380) f192 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 381) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 380), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bff) f192 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 382) (RestInside.exec (n := 382) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 380), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c04) f193 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 383) (RestInside.out (n := 383) f194 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 384) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 383), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c0a) f194 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 385) (RestInside.exec (n := 385) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 383), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c0f) f195 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 386) (RestInside.out (n := 386) f196 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 387) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 386), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c15) f196 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 388) (RestInside.exec (n := 388) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 386), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c1a) f197 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 389) (RestInside.out (n := 389) f198 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 390) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 389), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c20) f198 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 391) (RestInside.exec (n := 391) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 389), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c25) f199 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1087a5_10 code

theorem rest_l1087a5_8 [Bindings] (code : CodeMap) :
    Rest (n := 319) code lifted (codeRange 0x1087a5 bytes_l1087a5) [(0, 91), (1, 317), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]
      153 0x108b2f bytes_l1087a5_8 b_l1087a5_8 := by
  have f160 : InstrSpec 0x108b2f [0x32, 0x4C, 0x28, 0x32] (LoadPre 0x108b2f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x32)) s (0x108b2f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108b2f 4 1 (.sib 0 (some 5) 0 (.d8 0x32)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108b2f 4 1 (.sib 0 (some 5) 0 (.d8 0x32))).toInstrSpec (xor_r8_m8_effect_step 0x108b2f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x32)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f161 : InstrSpec 0x108b33 [0x88, 0x4C, 0x24, 0x49] (StorePre 0x108b33 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x49)) s (0x108b33 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108b33 4 1 (.sib 4 none 0 (.d8 0x49)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108b33 4 1 (.sib 4 none 0 (.d8 0x49))).toInstrSpec (mov_m8_r8_effect_step 0x108b33 1 (by decide) (.sib 4 none 0 (.d8 0x49)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f162 : InstrSpec 0x108b37 [0x0F, 0xB6, 0x8C, 0x24, 0xCB, 0x00, 0x00, 0x00] (LoadPre 0x108b37 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcb)) s (0x108b37 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108b37 8 1 (.sib 4 none 0 (.d32 0xcb)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108b37 8 1 (.sib 4 none 0 (.d32 0xcb))).toInstrSpec (movzx_r32_m8_effect_step 0x108b37 1 (.sib 4 none 0 (.d32 0xcb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f163 : InstrSpec 0x108b3f [0x32, 0x4C, 0x28, 0x33] (LoadPre 0x108b3f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x33)) s (0x108b3f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108b3f 4 1 (.sib 0 (some 5) 0 (.d8 0x33)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108b3f 4 1 (.sib 0 (some 5) 0 (.d8 0x33))).toInstrSpec (xor_r8_m8_effect_step 0x108b3f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x33)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f164 : InstrSpec 0x108b43 [0x88, 0x4C, 0x24, 0x48] (StorePre 0x108b43 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x108b43 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108b43 4 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108b43 4 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m8_r8_effect_step 0x108b43 1 (by decide) (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f165 : InstrSpec 0x108b47 [0x44, 0x0F, 0xB6, 0xA4, 0x24, 0xCC, 0x00, 0x00, 0x00] (LoadPre 0x108b47 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc)) s (0x108b47 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108b47 9 12 (.sib 4 none 0 (.d32 0xcc)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x108b47 9 12 (.sib 4 none 0 (.d32 0xcc))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108b47 0x44 (by decide) 4 (.sib 4 none 0 (.d32 0xcc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f166 : InstrSpec 0x108b50 [0x44, 0x32, 0x64, 0x28, 0x34] (LoadPre 0x108b50 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x34)) s (0x108b50 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108b50 5 12 (.sib 0 (some 5) 0 (.d8 0x34)))
      [.gpr 12, .gpr 0, .gpr 5] [] [.reg 12, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108b50 5 12 (.sib 0 (some 5) 0 (.d8 0x34))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108b50 0x44 (by decide) 4 (.sib 0 (some 5) 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f167 : InstrSpec 0x108b55 [0x44, 0x0F, 0xB6, 0xBC, 0x24, 0xCD, 0x00, 0x00, 0x00] (LoadPre 0x108b55 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcd)) s (0x108b55 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108b55 9 15 (.sib 4 none 0 (.d32 0xcd)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x108b55 9 15 (.sib 4 none 0 (.d32 0xcd))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108b55 0x44 (by decide) 7 (.sib 4 none 0 (.d32 0xcd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f168 : InstrSpec 0x108b5e [0x44, 0x32, 0x7C, 0x28, 0x35] (LoadPre 0x108b5e (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x35)) s (0x108b5e + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108b5e 5 15 (.sib 0 (some 5) 0 (.d8 0x35)))
      [.gpr 15, .gpr 0, .gpr 5] [] [.reg 15, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108b5e 5 15 (.sib 0 (some 5) 0 (.d8 0x35))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108b5e 0x44 (by decide) 7 (.sib 0 (some 5) 0 (.d8 0x35)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f169 : InstrSpec 0x108b63 [0x44, 0x0F, 0xB6, 0xB4, 0x24, 0xCE, 0x00, 0x00, 0x00] (LoadPre 0x108b63 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xce)) s (0x108b63 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108b63 9 14 (.sib 4 none 0 (.d32 0xce)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x108b63 9 14 (.sib 4 none 0 (.d32 0xce))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108b63 0x44 (by decide) 6 (.sib 4 none 0 (.d32 0xce)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f170 : InstrSpec 0x108b6c [0x44, 0x32, 0x74, 0x28, 0x36] (LoadPre 0x108b6c (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x36)) s (0x108b6c + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108b6c 5 14 (.sib 0 (some 5) 0 (.d8 0x36)))
      [.gpr 14, .gpr 0, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108b6c 5 14 (.sib 0 (some 5) 0 (.d8 0x36))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108b6c 0x44 (by decide) 6 (.sib 0 (some 5) 0 (.d8 0x36)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f171 : InstrSpec 0x108b71 [0x0F, 0xB6, 0x9C, 0x24, 0xCF, 0x00, 0x00, 0x00] (LoadPre 0x108b71 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcf)) s (0x108b71 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108b71 8 3 (.sib 4 none 0 (.d32 0xcf)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x108b71 8 3 (.sib 4 none 0 (.d32 0xcf))).toInstrSpec (movzx_r32_m8_effect_step 0x108b71 3 (.sib 4 none 0 (.d32 0xcf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f172 : InstrSpec 0x108b79 [0x32, 0x5C, 0x28, 0x37] (LoadPre 0x108b79 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x37)) s (0x108b79 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108b79 4 3 (.sib 0 (some 5) 0 (.d8 0x37)))
      [.gpr 3, .gpr 0, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108b79 4 3 (.sib 0 (some 5) 0 (.d8 0x37))).toInstrSpec (xor_r8_m8_effect_step 0x108b79 3 (by decide) (.sib 0 (some 5) 0 (.d8 0x37)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f173 : InstrSpec 0x108b7d [0x44, 0x0F, 0xB6, 0x9C, 0x24, 0xD0, 0x00, 0x00, 0x00] (LoadPre 0x108b7d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x108b7d + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108b7d 9 11 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x108b7d 9 11 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108b7d 0x44 (by decide) 3 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f174 : InstrSpec 0x108b86 [0x44, 0x32, 0x5C, 0x28, 0x38] (LoadPre 0x108b86 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x38)) s (0x108b86 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108b86 5 11 (.sib 0 (some 5) 0 (.d8 0x38)))
      [.gpr 11, .gpr 0, .gpr 5] [] [.reg 11, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108b86 5 11 (.sib 0 (some 5) 0 (.d8 0x38))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108b86 0x44 (by decide) 3 (.sib 0 (some 5) 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f175 : InstrSpec 0x108b8b [0x44, 0x0F, 0xB6, 0x94, 0x24, 0xD1, 0x00, 0x00, 0x00] (LoadPre 0x108b8b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd1)) s (0x108b8b + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108b8b 9 10 (.sib 4 none 0 (.d32 0xd1)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x108b8b 9 10 (.sib 4 none 0 (.d32 0xd1))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108b8b 0x44 (by decide) 2 (.sib 4 none 0 (.d32 0xd1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f176 : InstrSpec 0x108b94 [0x44, 0x32, 0x54, 0x28, 0x39] (LoadPre 0x108b94 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x39)) s (0x108b94 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108b94 5 10 (.sib 0 (some 5) 0 (.d8 0x39)))
      [.gpr 10, .gpr 0, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108b94 5 10 (.sib 0 (some 5) 0 (.d8 0x39))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108b94 0x44 (by decide) 2 (.sib 0 (some 5) 0 (.d8 0x39)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f177 : InstrSpec 0x108b99 [0x44, 0x0F, 0xB6, 0x8C, 0x24, 0xD2, 0x00, 0x00, 0x00] (LoadPre 0x108b99 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd2)) s (0x108b99 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108b99 9 9 (.sib 4 none 0 (.d32 0xd2)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x108b99 9 9 (.sib 4 none 0 (.d32 0xd2))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108b99 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0xd2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f178 : InstrSpec 0x108ba2 [0x44, 0x32, 0x4C, 0x28, 0x3A] (LoadPre 0x108ba2 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3a)) s (0x108ba2 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108ba2 5 9 (.sib 0 (some 5) 0 (.d8 0x3a)))
      [.gpr 9, .gpr 0, .gpr 5] [] [.reg 9, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108ba2 5 9 (.sib 0 (some 5) 0 (.d8 0x3a))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108ba2 0x44 (by decide) 1 (.sib 0 (some 5) 0 (.d8 0x3a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f179 : InstrSpec 0x108ba7 [0x44, 0x0F, 0xB6, 0x84, 0x24, 0xD3, 0x00, 0x00, 0x00] (LoadPre 0x108ba7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd3)) s (0x108ba7 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108ba7 9 8 (.sib 4 none 0 (.d32 0xd3)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x108ba7 9 8 (.sib 4 none 0 (.d32 0xd3))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108ba7 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0xd3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 319) (RestInside.out (n := 319) f160 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 320) (ρ' := [(0, 91), (1, 319), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b33) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 321) (RestInside.exec (n := 321) (ρ' := [(0, 91), (1, 319), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b37) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 322) (RestInside.out (n := 322) f162 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 323) (ρ' := [(0, 91), (1, 322), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b3f) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 324) (RestInside.out (n := 324) f163 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 325) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b43) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 326) (RestInside.exec (n := 326) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b47) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 327) (RestInside.out (n := 327) f165 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 328) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 327), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b50) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 329) (RestInside.out (n := 329) f166 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 330) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 329), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b55) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 331) (RestInside.out (n := 331) f167 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 332) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 329), (13, 129), (14, 120), (15, 331), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b5e) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 333) (RestInside.out (n := 333) f168 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 334) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 329), (13, 129), (14, 120), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b63) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 335) (RestInside.out (n := 335) f169 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 336) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 329), (13, 129), (14, 335), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b6c) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 337) (RestInside.out (n := 337) f170 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 338) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b71) f170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 339) (RestInside.out (n := 339) f171 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 340) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 339), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b79) f171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 341) (RestInside.out (n := 341) f172 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 342) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b7d) f172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 343) (RestInside.out (n := 343) f173 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 344) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 343), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b86) f173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 345) (RestInside.out (n := 345) f174 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 346) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b8b) f174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 347) (RestInside.out (n := 347) f175 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 348) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 347), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b94) f175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 349) (RestInside.out (n := 349) f176 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 350) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b99) f176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 351) (RestInside.out (n := 351) f177 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 352) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 351), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ba2) f177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 353) (RestInside.out (n := 353) f178 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 354) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ba7) f178 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 355) (RestInside.out (n := 355) f179 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 356) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 355), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bb0) f179 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1087a5_9 code

theorem rest_l1087a5_7 [Bindings] (code : CodeMap) :
    Rest (n := 286) code lifted (codeRange 0x1087a5 bytes_l1087a5) [(0, 91), (1, 284), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]
      173 0x108ac3 bytes_l1087a5_7 b_l1087a5_7 := by
  have f140 : InstrSpec 0x108ac3 [0x88, 0x4C, 0x24, 0x50] (StorePre 0x108ac3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x108ac3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108ac3 4 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108ac3 4 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m8_r8_effect_step 0x108ac3 1 (by decide) (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f141 : InstrSpec 0x108ac7 [0x0F, 0xB6, 0x8C, 0x24, 0xC4, 0x00, 0x00, 0x00] (LoadPre 0x108ac7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc4)) s (0x108ac7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108ac7 8 1 (.sib 4 none 0 (.d32 0xc4)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108ac7 8 1 (.sib 4 none 0 (.d32 0xc4))).toInstrSpec (movzx_r32_m8_effect_step 0x108ac7 1 (.sib 4 none 0 (.d32 0xc4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f142 : InstrSpec 0x108acf [0x32, 0x4C, 0x28, 0x2C] (LoadPre 0x108acf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2c)) s (0x108acf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108acf 4 1 (.sib 0 (some 5) 0 (.d8 0x2c)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108acf 4 1 (.sib 0 (some 5) 0 (.d8 0x2c))).toInstrSpec (xor_r8_m8_effect_step 0x108acf 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f143 : InstrSpec 0x108ad3 [0x88, 0x4C, 0x24, 0x4F] (StorePre 0x108ad3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x108ad3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108ad3 4 1 (.sib 4 none 0 (.d8 0x4f)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108ad3 4 1 (.sib 4 none 0 (.d8 0x4f))).toInstrSpec (mov_m8_r8_effect_step 0x108ad3 1 (by decide) (.sib 4 none 0 (.d8 0x4f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f144 : InstrSpec 0x108ad7 [0x0F, 0xB6, 0x8C, 0x24, 0xC5, 0x00, 0x00, 0x00] (LoadPre 0x108ad7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc5)) s (0x108ad7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108ad7 8 1 (.sib 4 none 0 (.d32 0xc5)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108ad7 8 1 (.sib 4 none 0 (.d32 0xc5))).toInstrSpec (movzx_r32_m8_effect_step 0x108ad7 1 (.sib 4 none 0 (.d32 0xc5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f145 : InstrSpec 0x108adf [0x32, 0x4C, 0x28, 0x2D] (LoadPre 0x108adf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2d)) s (0x108adf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108adf 4 1 (.sib 0 (some 5) 0 (.d8 0x2d)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108adf 4 1 (.sib 0 (some 5) 0 (.d8 0x2d))).toInstrSpec (xor_r8_m8_effect_step 0x108adf 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f146 : InstrSpec 0x108ae3 [0x88, 0x4C, 0x24, 0x4E] (StorePre 0x108ae3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4e)) s (0x108ae3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108ae3 4 1 (.sib 4 none 0 (.d8 0x4e)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108ae3 4 1 (.sib 4 none 0 (.d8 0x4e))).toInstrSpec (mov_m8_r8_effect_step 0x108ae3 1 (by decide) (.sib 4 none 0 (.d8 0x4e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f147 : InstrSpec 0x108ae7 [0x0F, 0xB6, 0x8C, 0x24, 0xC6, 0x00, 0x00, 0x00] (LoadPre 0x108ae7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc6)) s (0x108ae7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108ae7 8 1 (.sib 4 none 0 (.d32 0xc6)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108ae7 8 1 (.sib 4 none 0 (.d32 0xc6))).toInstrSpec (movzx_r32_m8_effect_step 0x108ae7 1 (.sib 4 none 0 (.d32 0xc6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f148 : InstrSpec 0x108aef [0x32, 0x4C, 0x28, 0x2E] (LoadPre 0x108aef (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2e)) s (0x108aef + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108aef 4 1 (.sib 0 (some 5) 0 (.d8 0x2e)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108aef 4 1 (.sib 0 (some 5) 0 (.d8 0x2e))).toInstrSpec (xor_r8_m8_effect_step 0x108aef 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x2e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f149 : InstrSpec 0x108af3 [0x88, 0x4C, 0x24, 0x4D] (StorePre 0x108af3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x108af3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108af3 4 1 (.sib 4 none 0 (.d8 0x4d)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108af3 4 1 (.sib 4 none 0 (.d8 0x4d))).toInstrSpec (mov_m8_r8_effect_step 0x108af3 1 (by decide) (.sib 4 none 0 (.d8 0x4d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f150 : InstrSpec 0x108af7 [0x0F, 0xB6, 0x8C, 0x24, 0xC7, 0x00, 0x00, 0x00] (LoadPre 0x108af7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc7)) s (0x108af7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108af7 8 1 (.sib 4 none 0 (.d32 0xc7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108af7 8 1 (.sib 4 none 0 (.d32 0xc7))).toInstrSpec (movzx_r32_m8_effect_step 0x108af7 1 (.sib 4 none 0 (.d32 0xc7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f151 : InstrSpec 0x108aff [0x32, 0x4C, 0x28, 0x2F] (LoadPre 0x108aff (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2f)) s (0x108aff + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108aff 4 1 (.sib 0 (some 5) 0 (.d8 0x2f)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108aff 4 1 (.sib 0 (some 5) 0 (.d8 0x2f))).toInstrSpec (xor_r8_m8_effect_step 0x108aff 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x2f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f152 : InstrSpec 0x108b03 [0x88, 0x4C, 0x24, 0x4C] (StorePre 0x108b03 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x108b03 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108b03 4 1 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108b03 4 1 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_m8_r8_effect_step 0x108b03 1 (by decide) (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f153 : InstrSpec 0x108b07 [0x0F, 0xB6, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x108b07 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x108b07 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108b07 8 1 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108b07 8 1 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (movzx_r32_m8_effect_step 0x108b07 1 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f154 : InstrSpec 0x108b0f [0x32, 0x4C, 0x28, 0x30] (LoadPre 0x108b0f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x30)) s (0x108b0f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108b0f 4 1 (.sib 0 (some 5) 0 (.d8 0x30)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108b0f 4 1 (.sib 0 (some 5) 0 (.d8 0x30))).toInstrSpec (xor_r8_m8_effect_step 0x108b0f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f155 : InstrSpec 0x108b13 [0x88, 0x4C, 0x24, 0x4B] (StorePre 0x108b13 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x108b13 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108b13 4 1 (.sib 4 none 0 (.d8 0x4b)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108b13 4 1 (.sib 4 none 0 (.d8 0x4b))).toInstrSpec (mov_m8_r8_effect_step 0x108b13 1 (by decide) (.sib 4 none 0 (.d8 0x4b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f156 : InstrSpec 0x108b17 [0x0F, 0xB6, 0x8C, 0x24, 0xC9, 0x00, 0x00, 0x00] (LoadPre 0x108b17 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc9)) s (0x108b17 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108b17 8 1 (.sib 4 none 0 (.d32 0xc9)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108b17 8 1 (.sib 4 none 0 (.d32 0xc9))).toInstrSpec (movzx_r32_m8_effect_step 0x108b17 1 (.sib 4 none 0 (.d32 0xc9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f157 : InstrSpec 0x108b1f [0x32, 0x4C, 0x28, 0x31] (LoadPre 0x108b1f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x31)) s (0x108b1f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108b1f 4 1 (.sib 0 (some 5) 0 (.d8 0x31)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108b1f 4 1 (.sib 0 (some 5) 0 (.d8 0x31))).toInstrSpec (xor_r8_m8_effect_step 0x108b1f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x31)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f158 : InstrSpec 0x108b23 [0x88, 0x4C, 0x24, 0x4A] (StorePre 0x108b23 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x108b23 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108b23 4 1 (.sib 4 none 0 (.d8 0x4a)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108b23 4 1 (.sib 4 none 0 (.d8 0x4a))).toInstrSpec (mov_m8_r8_effect_step 0x108b23 1 (by decide) (.sib 4 none 0 (.d8 0x4a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f159 : InstrSpec 0x108b27 [0x0F, 0xB6, 0x8C, 0x24, 0xCA, 0x00, 0x00, 0x00] (LoadPre 0x108b27 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xca)) s (0x108b27 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108b27 8 1 (.sib 4 none 0 (.d32 0xca)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108b27 8 1 (.sib 4 none 0 (.d32 0xca))).toInstrSpec (movzx_r32_m8_effect_step 0x108b27 1 (.sib 4 none 0 (.d32 0xca)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 286) (RestInside.exec (n := 286) (ρ' := [(0, 91), (1, 284), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ac7) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 287) (RestInside.out (n := 287) f141 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 288) (ρ' := [(0, 91), (1, 287), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108acf) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 289) (RestInside.out (n := 289) f142 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 290) (ρ' := [(0, 91), (1, 289), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ad3) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 291) (RestInside.exec (n := 291) (ρ' := [(0, 91), (1, 289), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ad7) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 292) (RestInside.out (n := 292) f144 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 293) (ρ' := [(0, 91), (1, 292), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108adf) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 294) (RestInside.out (n := 294) f145 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 295) (ρ' := [(0, 91), (1, 294), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ae3) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 296) (RestInside.exec (n := 296) (ρ' := [(0, 91), (1, 294), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ae7) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 297) (RestInside.out (n := 297) f147 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 298) (ρ' := [(0, 91), (1, 297), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108aef) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 299) (RestInside.out (n := 299) f148 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 300) (ρ' := [(0, 91), (1, 299), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108af3) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 301) (RestInside.exec (n := 301) (ρ' := [(0, 91), (1, 299), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108af7) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f150 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 303) (ρ' := [(0, 91), (1, 302), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108aff) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f151 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 305) (ρ' := [(0, 91), (1, 304), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b03) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 306) (RestInside.exec (n := 306) (ρ' := [(0, 91), (1, 304), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b07) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 307) (RestInside.out (n := 307) f153 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 308) (ρ' := [(0, 91), (1, 307), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b0f) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 309) (RestInside.out (n := 309) f154 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 310) (ρ' := [(0, 91), (1, 309), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b13) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 311) (RestInside.exec (n := 311) (ρ' := [(0, 91), (1, 309), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b17) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 312) (RestInside.out (n := 312) f156 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 313) (ρ' := [(0, 91), (1, 312), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b1f) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 314) (RestInside.out (n := 314) f157 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 315) (ρ' := [(0, 91), (1, 314), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b23) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 316) (RestInside.exec (n := 316) (ρ' := [(0, 91), (1, 314), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b27) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 317) (RestInside.out (n := 317) f159 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 318) (ρ' := [(0, 91), (1, 317), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b2f) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1087a5_8 code

theorem rest_l1087a5_6 [Bindings] (code : CodeMap) :
    Rest (n := 252) code lifted (codeRange 0x1087a5 bytes_l1087a5) [(0, 91), (1, 249), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]
      193 0x108a57 bytes_l1087a5_6 b_l1087a5_6 := by
  have f120 : InstrSpec 0x108a57 [0x0F, 0xB6, 0x8C, 0x24, 0xBD, 0x00, 0x00, 0x00] (LoadPre 0x108a57 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbd)) s (0x108a57 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a57 8 1 (.sib 4 none 0 (.d32 0xbd)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108a57 8 1 (.sib 4 none 0 (.d32 0xbd))).toInstrSpec (movzx_r32_m8_effect_step 0x108a57 1 (.sib 4 none 0 (.d32 0xbd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f121 : InstrSpec 0x108a5f [0x32, 0x4C, 0x28, 0x25] (LoadPre 0x108a5f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x25)) s (0x108a5f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a5f 4 1 (.sib 0 (some 5) 0 (.d8 0x25)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108a5f 4 1 (.sib 0 (some 5) 0 (.d8 0x25))).toInstrSpec (xor_r8_m8_effect_step 0x108a5f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f122 : InstrSpec 0x108a63 [0x88, 0x4C, 0x24, 0x56] (StorePre 0x108a63 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x56)) s (0x108a63 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a63 4 1 (.sib 4 none 0 (.d8 0x56)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108a63 4 1 (.sib 4 none 0 (.d8 0x56))).toInstrSpec (mov_m8_r8_effect_step 0x108a63 1 (by decide) (.sib 4 none 0 (.d8 0x56)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f123 : InstrSpec 0x108a67 [0x0F, 0xB6, 0x8C, 0x24, 0xBE, 0x00, 0x00, 0x00] (LoadPre 0x108a67 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbe)) s (0x108a67 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a67 8 1 (.sib 4 none 0 (.d32 0xbe)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108a67 8 1 (.sib 4 none 0 (.d32 0xbe))).toInstrSpec (movzx_r32_m8_effect_step 0x108a67 1 (.sib 4 none 0 (.d32 0xbe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f124 : InstrSpec 0x108a6f [0x32, 0x4C, 0x28, 0x26] (LoadPre 0x108a6f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x26)) s (0x108a6f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a6f 4 1 (.sib 0 (some 5) 0 (.d8 0x26)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108a6f 4 1 (.sib 0 (some 5) 0 (.d8 0x26))).toInstrSpec (xor_r8_m8_effect_step 0x108a6f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x26)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f125 : InstrSpec 0x108a73 [0x88, 0x4C, 0x24, 0x55] (StorePre 0x108a73 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x55)) s (0x108a73 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a73 4 1 (.sib 4 none 0 (.d8 0x55)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108a73 4 1 (.sib 4 none 0 (.d8 0x55))).toInstrSpec (mov_m8_r8_effect_step 0x108a73 1 (by decide) (.sib 4 none 0 (.d8 0x55)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f126 : InstrSpec 0x108a77 [0x0F, 0xB6, 0x8C, 0x24, 0xBF, 0x00, 0x00, 0x00] (LoadPre 0x108a77 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbf)) s (0x108a77 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a77 8 1 (.sib 4 none 0 (.d32 0xbf)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108a77 8 1 (.sib 4 none 0 (.d32 0xbf))).toInstrSpec (movzx_r32_m8_effect_step 0x108a77 1 (.sib 4 none 0 (.d32 0xbf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f127 : InstrSpec 0x108a7f [0x32, 0x4C, 0x28, 0x27] (LoadPre 0x108a7f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x27)) s (0x108a7f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a7f 4 1 (.sib 0 (some 5) 0 (.d8 0x27)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108a7f 4 1 (.sib 0 (some 5) 0 (.d8 0x27))).toInstrSpec (xor_r8_m8_effect_step 0x108a7f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x27)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f128 : InstrSpec 0x108a83 [0x88, 0x4C, 0x24, 0x54] (StorePre 0x108a83 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x108a83 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a83 4 1 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108a83 4 1 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_m8_r8_effect_step 0x108a83 1 (by decide) (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f129 : InstrSpec 0x108a87 [0x0F, 0xB6, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x108a87 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x108a87 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a87 8 1 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108a87 8 1 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (movzx_r32_m8_effect_step 0x108a87 1 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f130 : InstrSpec 0x108a8f [0x32, 0x4C, 0x28, 0x28] (LoadPre 0x108a8f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x28)) s (0x108a8f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a8f 4 1 (.sib 0 (some 5) 0 (.d8 0x28)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108a8f 4 1 (.sib 0 (some 5) 0 (.d8 0x28))).toInstrSpec (xor_r8_m8_effect_step 0x108a8f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f131 : InstrSpec 0x108a93 [0x88, 0x4C, 0x24, 0x53] (StorePre 0x108a93 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x108a93 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a93 4 1 (.sib 4 none 0 (.d8 0x53)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108a93 4 1 (.sib 4 none 0 (.d8 0x53))).toInstrSpec (mov_m8_r8_effect_step 0x108a93 1 (by decide) (.sib 4 none 0 (.d8 0x53)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f132 : InstrSpec 0x108a97 [0x0F, 0xB6, 0x8C, 0x24, 0xC1, 0x00, 0x00, 0x00] (LoadPre 0x108a97 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc1)) s (0x108a97 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a97 8 1 (.sib 4 none 0 (.d32 0xc1)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108a97 8 1 (.sib 4 none 0 (.d32 0xc1))).toInstrSpec (movzx_r32_m8_effect_step 0x108a97 1 (.sib 4 none 0 (.d32 0xc1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f133 : InstrSpec 0x108a9f [0x32, 0x4C, 0x28, 0x29] (LoadPre 0x108a9f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x29)) s (0x108a9f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a9f 4 1 (.sib 0 (some 5) 0 (.d8 0x29)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108a9f 4 1 (.sib 0 (some 5) 0 (.d8 0x29))).toInstrSpec (xor_r8_m8_effect_step 0x108a9f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x29)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f134 : InstrSpec 0x108aa3 [0x88, 0x4C, 0x24, 0x52] (StorePre 0x108aa3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x52)) s (0x108aa3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108aa3 4 1 (.sib 4 none 0 (.d8 0x52)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108aa3 4 1 (.sib 4 none 0 (.d8 0x52))).toInstrSpec (mov_m8_r8_effect_step 0x108aa3 1 (by decide) (.sib 4 none 0 (.d8 0x52)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f135 : InstrSpec 0x108aa7 [0x0F, 0xB6, 0x8C, 0x24, 0xC2, 0x00, 0x00, 0x00] (LoadPre 0x108aa7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc2)) s (0x108aa7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108aa7 8 1 (.sib 4 none 0 (.d32 0xc2)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108aa7 8 1 (.sib 4 none 0 (.d32 0xc2))).toInstrSpec (movzx_r32_m8_effect_step 0x108aa7 1 (.sib 4 none 0 (.d32 0xc2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f136 : InstrSpec 0x108aaf [0x32, 0x4C, 0x28, 0x2A] (LoadPre 0x108aaf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2a)) s (0x108aaf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108aaf 4 1 (.sib 0 (some 5) 0 (.d8 0x2a)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108aaf 4 1 (.sib 0 (some 5) 0 (.d8 0x2a))).toInstrSpec (xor_r8_m8_effect_step 0x108aaf 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x2a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f137 : InstrSpec 0x108ab3 [0x88, 0x4C, 0x24, 0x51] (StorePre 0x108ab3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x51)) s (0x108ab3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108ab3 4 1 (.sib 4 none 0 (.d8 0x51)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108ab3 4 1 (.sib 4 none 0 (.d8 0x51))).toInstrSpec (mov_m8_r8_effect_step 0x108ab3 1 (by decide) (.sib 4 none 0 (.d8 0x51)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f138 : InstrSpec 0x108ab7 [0x0F, 0xB6, 0x8C, 0x24, 0xC3, 0x00, 0x00, 0x00] (LoadPre 0x108ab7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc3)) s (0x108ab7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108ab7 8 1 (.sib 4 none 0 (.d32 0xc3)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108ab7 8 1 (.sib 4 none 0 (.d32 0xc3))).toInstrSpec (movzx_r32_m8_effect_step 0x108ab7 1 (.sib 4 none 0 (.d32 0xc3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f139 : InstrSpec 0x108abf [0x32, 0x4C, 0x28, 0x2B] (LoadPre 0x108abf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2b)) s (0x108abf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108abf 4 1 (.sib 0 (some 5) 0 (.d8 0x2b)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108abf 4 1 (.sib 0 (some 5) 0 (.d8 0x2b))).toInstrSpec (xor_r8_m8_effect_step 0x108abf 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x2b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 252) (RestInside.out (n := 252) f120 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 253) (ρ' := [(0, 91), (1, 252), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a5f) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 254) (RestInside.out (n := 254) f121 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 255) (ρ' := [(0, 91), (1, 254), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a63) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 256) (RestInside.exec (n := 256) (ρ' := [(0, 91), (1, 254), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a67) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 257) (RestInside.out (n := 257) f123 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 258) (ρ' := [(0, 91), (1, 257), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a6f) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f124 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 260) (ρ' := [(0, 91), (1, 259), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a73) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 261) (RestInside.exec (n := 261) (ρ' := [(0, 91), (1, 259), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a77) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 262) (RestInside.out (n := 262) f126 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 263) (ρ' := [(0, 91), (1, 262), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a7f) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 264) (RestInside.out (n := 264) f127 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 265) (ρ' := [(0, 91), (1, 264), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a83) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 266) (RestInside.exec (n := 266) (ρ' := [(0, 91), (1, 264), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a87) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 267) (RestInside.out (n := 267) f129 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 268) (ρ' := [(0, 91), (1, 267), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a8f) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 269) (RestInside.out (n := 269) f130 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 270) (ρ' := [(0, 91), (1, 269), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a93) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 271) (RestInside.exec (n := 271) (ρ' := [(0, 91), (1, 269), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a97) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 272) (RestInside.out (n := 272) f132 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 273) (ρ' := [(0, 91), (1, 272), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a9f) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 274) (RestInside.out (n := 274) f133 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 275) (ρ' := [(0, 91), (1, 274), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108aa3) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 276) (RestInside.exec (n := 276) (ρ' := [(0, 91), (1, 274), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108aa7) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 277) (RestInside.out (n := 277) f135 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 278) (ρ' := [(0, 91), (1, 277), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108aaf) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 279) (RestInside.out (n := 279) f136 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 280) (ρ' := [(0, 91), (1, 279), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ab3) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 281) (RestInside.exec (n := 281) (ρ' := [(0, 91), (1, 279), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ab7) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 282) (RestInside.out (n := 282) f138 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 283) (ρ' := [(0, 91), (1, 282), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108abf) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 284) (RestInside.out (n := 284) f139 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 285) (ρ' := [(0, 91), (1, 284), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ac3) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1087a5_7 code

theorem rest_l1087a5_5 [Bindings] (code : CodeMap) :
    Rest (n := 219) code lifted (codeRange 0x1087a5 bytes_l1087a5) [(0, 91), (1, 217), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]
      213 0x1089ef bytes_l1087a5_5 b_l1087a5_5 := by
  have f100 : InstrSpec 0x1089ef [0x32, 0x4C, 0x28, 0x1E] (LoadPre 0x1089ef (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1e)) s (0x1089ef + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1089ef 4 1 (.sib 0 (some 5) 0 (.d8 0x1e)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1089ef 4 1 (.sib 0 (some 5) 0 (.d8 0x1e))).toInstrSpec (xor_r8_m8_effect_step 0x1089ef 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f101 : InstrSpec 0x1089f3 [0x88, 0x4C, 0x24, 0x5D] (StorePre 0x1089f3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5d)) s (0x1089f3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1089f3 4 1 (.sib 4 none 0 (.d8 0x5d)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1089f3 4 1 (.sib 4 none 0 (.d8 0x5d))).toInstrSpec (mov_m8_r8_effect_step 0x1089f3 1 (by decide) (.sib 4 none 0 (.d8 0x5d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f102 : InstrSpec 0x1089f7 [0x0F, 0xB6, 0x8C, 0x24, 0xB7, 0x00, 0x00, 0x00] (LoadPre 0x1089f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb7)) s (0x1089f7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1089f7 8 1 (.sib 4 none 0 (.d32 0xb7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1089f7 8 1 (.sib 4 none 0 (.d32 0xb7))).toInstrSpec (movzx_r32_m8_effect_step 0x1089f7 1 (.sib 4 none 0 (.d32 0xb7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f103 : InstrSpec 0x1089ff [0x32, 0x4C, 0x28, 0x1F] (LoadPre 0x1089ff (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1f)) s (0x1089ff + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1089ff 4 1 (.sib 0 (some 5) 0 (.d8 0x1f)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1089ff 4 1 (.sib 0 (some 5) 0 (.d8 0x1f))).toInstrSpec (xor_r8_m8_effect_step 0x1089ff 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f104 : InstrSpec 0x108a03 [0x88, 0x4C, 0x24, 0x5C] (StorePre 0x108a03 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x108a03 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a03 4 1 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108a03 4 1 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (mov_m8_r8_effect_step 0x108a03 1 (by decide) (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f105 : InstrSpec 0x108a07 [0x0F, 0xB6, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x108a07 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x108a07 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a07 8 1 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108a07 8 1 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (movzx_r32_m8_effect_step 0x108a07 1 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f106 : InstrSpec 0x108a0f [0x32, 0x4C, 0x28, 0x20] (LoadPre 0x108a0f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x20)) s (0x108a0f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a0f 4 1 (.sib 0 (some 5) 0 (.d8 0x20)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108a0f 4 1 (.sib 0 (some 5) 0 (.d8 0x20))).toInstrSpec (xor_r8_m8_effect_step 0x108a0f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f107 : InstrSpec 0x108a13 [0x88, 0x4C, 0x24, 0x5B] (StorePre 0x108a13 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5b)) s (0x108a13 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a13 4 1 (.sib 4 none 0 (.d8 0x5b)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108a13 4 1 (.sib 4 none 0 (.d8 0x5b))).toInstrSpec (mov_m8_r8_effect_step 0x108a13 1 (by decide) (.sib 4 none 0 (.d8 0x5b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f108 : InstrSpec 0x108a17 [0x0F, 0xB6, 0x8C, 0x24, 0xB9, 0x00, 0x00, 0x00] (LoadPre 0x108a17 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb9)) s (0x108a17 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a17 8 1 (.sib 4 none 0 (.d32 0xb9)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108a17 8 1 (.sib 4 none 0 (.d32 0xb9))).toInstrSpec (movzx_r32_m8_effect_step 0x108a17 1 (.sib 4 none 0 (.d32 0xb9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f109 : InstrSpec 0x108a1f [0x32, 0x4C, 0x28, 0x21] (LoadPre 0x108a1f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x21)) s (0x108a1f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a1f 4 1 (.sib 0 (some 5) 0 (.d8 0x21)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108a1f 4 1 (.sib 0 (some 5) 0 (.d8 0x21))).toInstrSpec (xor_r8_m8_effect_step 0x108a1f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x21)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f110 : InstrSpec 0x108a23 [0x88, 0x4C, 0x24, 0x5A] (StorePre 0x108a23 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5a)) s (0x108a23 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a23 4 1 (.sib 4 none 0 (.d8 0x5a)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108a23 4 1 (.sib 4 none 0 (.d8 0x5a))).toInstrSpec (mov_m8_r8_effect_step 0x108a23 1 (by decide) (.sib 4 none 0 (.d8 0x5a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f111 : InstrSpec 0x108a27 [0x0F, 0xB6, 0x8C, 0x24, 0xBA, 0x00, 0x00, 0x00] (LoadPre 0x108a27 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xba)) s (0x108a27 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a27 8 1 (.sib 4 none 0 (.d32 0xba)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108a27 8 1 (.sib 4 none 0 (.d32 0xba))).toInstrSpec (movzx_r32_m8_effect_step 0x108a27 1 (.sib 4 none 0 (.d32 0xba)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f112 : InstrSpec 0x108a2f [0x32, 0x4C, 0x28, 0x22] (LoadPre 0x108a2f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x22)) s (0x108a2f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a2f 4 1 (.sib 0 (some 5) 0 (.d8 0x22)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108a2f 4 1 (.sib 0 (some 5) 0 (.d8 0x22))).toInstrSpec (xor_r8_m8_effect_step 0x108a2f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x22)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f113 : InstrSpec 0x108a33 [0x88, 0x4C, 0x24, 0x59] (StorePre 0x108a33 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x59)) s (0x108a33 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a33 4 1 (.sib 4 none 0 (.d8 0x59)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108a33 4 1 (.sib 4 none 0 (.d8 0x59))).toInstrSpec (mov_m8_r8_effect_step 0x108a33 1 (by decide) (.sib 4 none 0 (.d8 0x59)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f114 : InstrSpec 0x108a37 [0x0F, 0xB6, 0x8C, 0x24, 0xBB, 0x00, 0x00, 0x00] (LoadPre 0x108a37 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbb)) s (0x108a37 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a37 8 1 (.sib 4 none 0 (.d32 0xbb)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108a37 8 1 (.sib 4 none 0 (.d32 0xbb))).toInstrSpec (movzx_r32_m8_effect_step 0x108a37 1 (.sib 4 none 0 (.d32 0xbb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f115 : InstrSpec 0x108a3f [0x32, 0x4C, 0x28, 0x23] (LoadPre 0x108a3f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x23)) s (0x108a3f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a3f 4 1 (.sib 0 (some 5) 0 (.d8 0x23)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108a3f 4 1 (.sib 0 (some 5) 0 (.d8 0x23))).toInstrSpec (xor_r8_m8_effect_step 0x108a3f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x23)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f116 : InstrSpec 0x108a43 [0x88, 0x4C, 0x24, 0x58] (StorePre 0x108a43 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x108a43 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a43 4 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108a43 4 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m8_r8_effect_step 0x108a43 1 (by decide) (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f117 : InstrSpec 0x108a47 [0x0F, 0xB6, 0x8C, 0x24, 0xBC, 0x00, 0x00, 0x00] (LoadPre 0x108a47 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbc)) s (0x108a47 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a47 8 1 (.sib 4 none 0 (.d32 0xbc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108a47 8 1 (.sib 4 none 0 (.d32 0xbc))).toInstrSpec (movzx_r32_m8_effect_step 0x108a47 1 (.sib 4 none 0 (.d32 0xbc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f118 : InstrSpec 0x108a4f [0x32, 0x4C, 0x28, 0x24] (LoadPre 0x108a4f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x24)) s (0x108a4f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a4f 4 1 (.sib 0 (some 5) 0 (.d8 0x24)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108a4f 4 1 (.sib 0 (some 5) 0 (.d8 0x24))).toInstrSpec (xor_r8_m8_effect_step 0x108a4f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f119 : InstrSpec 0x108a53 [0x88, 0x4C, 0x24, 0x57] (StorePre 0x108a53 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x57)) s (0x108a53 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a53 4 1 (.sib 4 none 0 (.d8 0x57)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108a53 4 1 (.sib 4 none 0 (.d8 0x57))).toInstrSpec (mov_m8_r8_effect_step 0x108a53 1 (by decide) (.sib 4 none 0 (.d8 0x57)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f100 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 91), (1, 219), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089f3) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.exec (n := 221) (ρ' := [(0, 91), (1, 219), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089f7) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 222) (RestInside.out (n := 222) f102 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 223) (ρ' := [(0, 91), (1, 222), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089ff) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 224) (RestInside.out (n := 224) f103 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 225) (ρ' := [(0, 91), (1, 224), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a03) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 226) (RestInside.exec (n := 226) (ρ' := [(0, 91), (1, 224), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a07) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f105 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 91), (1, 227), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a0f) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.out (n := 229) f106 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 230) (ρ' := [(0, 91), (1, 229), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a13) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.exec (n := 231) (ρ' := [(0, 91), (1, 229), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a17) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 232) (RestInside.out (n := 232) f108 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 233) (ρ' := [(0, 91), (1, 232), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a1f) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f109 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 91), (1, 234), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a23) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.exec (n := 236) (ρ' := [(0, 91), (1, 234), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a27) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 237) (RestInside.out (n := 237) f111 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 238) (ρ' := [(0, 91), (1, 237), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a2f) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 239) (RestInside.out (n := 239) f112 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 240) (ρ' := [(0, 91), (1, 239), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a33) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 241) (RestInside.exec (n := 241) (ρ' := [(0, 91), (1, 239), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a37) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 242) (RestInside.out (n := 242) f114 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 243) (ρ' := [(0, 91), (1, 242), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a3f) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 244) (RestInside.out (n := 244) f115 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 245) (ρ' := [(0, 91), (1, 244), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a43) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 246) (RestInside.exec (n := 246) (ρ' := [(0, 91), (1, 244), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a47) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f117 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 248) (ρ' := [(0, 91), (1, 247), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a4f) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 249) (RestInside.out (n := 249) f118 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 250) (ρ' := [(0, 91), (1, 249), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a53) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 251) (RestInside.exec (n := 251) (ρ' := [(0, 91), (1, 249), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a57) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1087a5_6 code

theorem rest_l1087a5_4 [Bindings] (code : CodeMap) :
    Rest (n := 186) code lifted (codeRange 0x1087a5 bytes_l1087a5) [(0, 91), (1, 184), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]
      233 0x108983 bytes_l1087a5_4 b_l1087a5_4 := by
  have f80 : InstrSpec 0x108983 [0x88, 0x4C, 0x24, 0x64] (StorePre 0x108983 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x108983 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108983 4 1 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108983 4 1 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (mov_m8_r8_effect_step 0x108983 1 (by decide) (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f81 : InstrSpec 0x108987 [0x0F, 0xB6, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x108987 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x108987 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108987 8 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108987 8 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (movzx_r32_m8_effect_step 0x108987 1 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f82 : InstrSpec 0x10898f [0x32, 0x4C, 0x28, 0x18] (LoadPre 0x10898f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x18)) s (0x10898f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10898f 4 1 (.sib 0 (some 5) 0 (.d8 0x18)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10898f 4 1 (.sib 0 (some 5) 0 (.d8 0x18))).toInstrSpec (xor_r8_m8_effect_step 0x10898f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f83 : InstrSpec 0x108993 [0x88, 0x4C, 0x24, 0x63] (StorePre 0x108993 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x63)) s (0x108993 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108993 4 1 (.sib 4 none 0 (.d8 0x63)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108993 4 1 (.sib 4 none 0 (.d8 0x63))).toInstrSpec (mov_m8_r8_effect_step 0x108993 1 (by decide) (.sib 4 none 0 (.d8 0x63)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f84 : InstrSpec 0x108997 [0x0F, 0xB6, 0x8C, 0x24, 0xB1, 0x00, 0x00, 0x00] (LoadPre 0x108997 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb1)) s (0x108997 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108997 8 1 (.sib 4 none 0 (.d32 0xb1)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108997 8 1 (.sib 4 none 0 (.d32 0xb1))).toInstrSpec (movzx_r32_m8_effect_step 0x108997 1 (.sib 4 none 0 (.d32 0xb1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f85 : InstrSpec 0x10899f [0x32, 0x4C, 0x28, 0x19] (LoadPre 0x10899f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x19)) s (0x10899f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10899f 4 1 (.sib 0 (some 5) 0 (.d8 0x19)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10899f 4 1 (.sib 0 (some 5) 0 (.d8 0x19))).toInstrSpec (xor_r8_m8_effect_step 0x10899f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f86 : InstrSpec 0x1089a3 [0x88, 0x4C, 0x24, 0x62] (StorePre 0x1089a3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x1089a3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1089a3 4 1 (.sib 4 none 0 (.d8 0x62)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1089a3 4 1 (.sib 4 none 0 (.d8 0x62))).toInstrSpec (mov_m8_r8_effect_step 0x1089a3 1 (by decide) (.sib 4 none 0 (.d8 0x62)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f87 : InstrSpec 0x1089a7 [0x0F, 0xB6, 0x8C, 0x24, 0xB2, 0x00, 0x00, 0x00] (LoadPre 0x1089a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb2)) s (0x1089a7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1089a7 8 1 (.sib 4 none 0 (.d32 0xb2)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1089a7 8 1 (.sib 4 none 0 (.d32 0xb2))).toInstrSpec (movzx_r32_m8_effect_step 0x1089a7 1 (.sib 4 none 0 (.d32 0xb2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f88 : InstrSpec 0x1089af [0x32, 0x4C, 0x28, 0x1A] (LoadPre 0x1089af (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1a)) s (0x1089af + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1089af 4 1 (.sib 0 (some 5) 0 (.d8 0x1a)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1089af 4 1 (.sib 0 (some 5) 0 (.d8 0x1a))).toInstrSpec (xor_r8_m8_effect_step 0x1089af 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f89 : InstrSpec 0x1089b3 [0x88, 0x4C, 0x24, 0x61] (StorePre 0x1089b3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x61)) s (0x1089b3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1089b3 4 1 (.sib 4 none 0 (.d8 0x61)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1089b3 4 1 (.sib 4 none 0 (.d8 0x61))).toInstrSpec (mov_m8_r8_effect_step 0x1089b3 1 (by decide) (.sib 4 none 0 (.d8 0x61)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f90 : InstrSpec 0x1089b7 [0x0F, 0xB6, 0x8C, 0x24, 0xB3, 0x00, 0x00, 0x00] (LoadPre 0x1089b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb3)) s (0x1089b7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1089b7 8 1 (.sib 4 none 0 (.d32 0xb3)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1089b7 8 1 (.sib 4 none 0 (.d32 0xb3))).toInstrSpec (movzx_r32_m8_effect_step 0x1089b7 1 (.sib 4 none 0 (.d32 0xb3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f91 : InstrSpec 0x1089bf [0x32, 0x4C, 0x28, 0x1B] (LoadPre 0x1089bf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1b)) s (0x1089bf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1089bf 4 1 (.sib 0 (some 5) 0 (.d8 0x1b)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1089bf 4 1 (.sib 0 (some 5) 0 (.d8 0x1b))).toInstrSpec (xor_r8_m8_effect_step 0x1089bf 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f92 : InstrSpec 0x1089c3 [0x88, 0x4C, 0x24, 0x60] (StorePre 0x1089c3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1089c3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1089c3 4 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1089c3 4 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m8_r8_effect_step 0x1089c3 1 (by decide) (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f93 : InstrSpec 0x1089c7 [0x0F, 0xB6, 0x8C, 0x24, 0xB4, 0x00, 0x00, 0x00] (LoadPre 0x1089c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x1089c7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1089c7 8 1 (.sib 4 none 0 (.d32 0xb4)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1089c7 8 1 (.sib 4 none 0 (.d32 0xb4))).toInstrSpec (movzx_r32_m8_effect_step 0x1089c7 1 (.sib 4 none 0 (.d32 0xb4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f94 : InstrSpec 0x1089cf [0x32, 0x4C, 0x28, 0x1C] (LoadPre 0x1089cf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1c)) s (0x1089cf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1089cf 4 1 (.sib 0 (some 5) 0 (.d8 0x1c)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1089cf 4 1 (.sib 0 (some 5) 0 (.d8 0x1c))).toInstrSpec (xor_r8_m8_effect_step 0x1089cf 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f95 : InstrSpec 0x1089d3 [0x88, 0x4C, 0x24, 0x5F] (StorePre 0x1089d3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5f)) s (0x1089d3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1089d3 4 1 (.sib 4 none 0 (.d8 0x5f)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1089d3 4 1 (.sib 4 none 0 (.d8 0x5f))).toInstrSpec (mov_m8_r8_effect_step 0x1089d3 1 (by decide) (.sib 4 none 0 (.d8 0x5f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f96 : InstrSpec 0x1089d7 [0x0F, 0xB6, 0x8C, 0x24, 0xB5, 0x00, 0x00, 0x00] (LoadPre 0x1089d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb5)) s (0x1089d7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1089d7 8 1 (.sib 4 none 0 (.d32 0xb5)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1089d7 8 1 (.sib 4 none 0 (.d32 0xb5))).toInstrSpec (movzx_r32_m8_effect_step 0x1089d7 1 (.sib 4 none 0 (.d32 0xb5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f97 : InstrSpec 0x1089df [0x32, 0x4C, 0x28, 0x1D] (LoadPre 0x1089df (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1d)) s (0x1089df + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1089df 4 1 (.sib 0 (some 5) 0 (.d8 0x1d)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1089df 4 1 (.sib 0 (some 5) 0 (.d8 0x1d))).toInstrSpec (xor_r8_m8_effect_step 0x1089df 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f98 : InstrSpec 0x1089e3 [0x88, 0x4C, 0x24, 0x5E] (StorePre 0x1089e3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x1089e3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1089e3 4 1 (.sib 4 none 0 (.d8 0x5e)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1089e3 4 1 (.sib 4 none 0 (.d8 0x5e))).toInstrSpec (mov_m8_r8_effect_step 0x1089e3 1 (by decide) (.sib 4 none 0 (.d8 0x5e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f99 : InstrSpec 0x1089e7 [0x0F, 0xB6, 0x8C, 0x24, 0xB6, 0x00, 0x00, 0x00] (LoadPre 0x1089e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb6)) s (0x1089e7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1089e7 8 1 (.sib 4 none 0 (.d32 0xb6)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1089e7 8 1 (.sib 4 none 0 (.d32 0xb6))).toInstrSpec (movzx_r32_m8_effect_step 0x1089e7 1 (.sib 4 none 0 (.d32 0xb6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 186) (RestInside.exec (n := 186) (ρ' := [(0, 91), (1, 184), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108987) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f81 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 91), (1, 187), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10898f) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f82 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 91), (1, 189), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108993) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.exec (n := 191) (ρ' := [(0, 91), (1, 189), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108997) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 192) (RestInside.out (n := 192) f84 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 193) (ρ' := [(0, 91), (1, 192), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10899f) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 194) (RestInside.out (n := 194) f85 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 195) (ρ' := [(0, 91), (1, 194), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089a3) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 196) (RestInside.exec (n := 196) (ρ' := [(0, 91), (1, 194), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089a7) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f87 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 91), (1, 197), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089af) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f88 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 91), (1, 199), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089b3) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.exec (n := 201) (ρ' := [(0, 91), (1, 199), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089b7) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f90 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 91), (1, 202), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089bf) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f91 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 91), (1, 204), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089c3) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.exec (n := 206) (ρ' := [(0, 91), (1, 204), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089c7) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 207) (RestInside.out (n := 207) f93 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 208) (ρ' := [(0, 91), (1, 207), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089cf) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 209) (RestInside.out (n := 209) f94 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 210) (ρ' := [(0, 91), (1, 209), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089d3) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 211) (RestInside.exec (n := 211) (ρ' := [(0, 91), (1, 209), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089d7) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f96 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 91), (1, 212), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089df) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f97 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 91), (1, 214), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089e3) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.exec (n := 216) (ρ' := [(0, 91), (1, 214), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089e7) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 217) (RestInside.out (n := 217) f99 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 218) (ρ' := [(0, 91), (1, 217), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089ef) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1087a5_5 code

theorem rest_l1087a5_3 [Bindings] (code : CodeMap) :
    Rest (n := 152) code lifted (codeRange 0x1087a5 bytes_l1087a5) [(0, 91), (1, 149), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]
      253 0x108917 bytes_l1087a5_3 b_l1087a5_3 := by
  have f60 : InstrSpec 0x108917 [0x0F, 0xB6, 0x8C, 0x24, 0xA9, 0x00, 0x00, 0x00] (LoadPre 0x108917 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa9)) s (0x108917 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108917 8 1 (.sib 4 none 0 (.d32 0xa9)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108917 8 1 (.sib 4 none 0 (.d32 0xa9))).toInstrSpec (movzx_r32_m8_effect_step 0x108917 1 (.sib 4 none 0 (.d32 0xa9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f61 : InstrSpec 0x10891f [0x32, 0x4C, 0x28, 0x11] (LoadPre 0x10891f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x11)) s (0x10891f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10891f 4 1 (.sib 0 (some 5) 0 (.d8 0x11)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10891f 4 1 (.sib 0 (some 5) 0 (.d8 0x11))).toInstrSpec (xor_r8_m8_effect_step 0x10891f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f62 : InstrSpec 0x108923 [0x88, 0x4C, 0x24, 0x6A] (StorePre 0x108923 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6a)) s (0x108923 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108923 4 1 (.sib 4 none 0 (.d8 0x6a)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108923 4 1 (.sib 4 none 0 (.d8 0x6a))).toInstrSpec (mov_m8_r8_effect_step 0x108923 1 (by decide) (.sib 4 none 0 (.d8 0x6a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f63 : InstrSpec 0x108927 [0x0F, 0xB6, 0x8C, 0x24, 0xAA, 0x00, 0x00, 0x00] (LoadPre 0x108927 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaa)) s (0x108927 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108927 8 1 (.sib 4 none 0 (.d32 0xaa)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108927 8 1 (.sib 4 none 0 (.d32 0xaa))).toInstrSpec (movzx_r32_m8_effect_step 0x108927 1 (.sib 4 none 0 (.d32 0xaa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f64 : InstrSpec 0x10892f [0x32, 0x4C, 0x28, 0x12] (LoadPre 0x10892f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x12)) s (0x10892f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10892f 4 1 (.sib 0 (some 5) 0 (.d8 0x12)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10892f 4 1 (.sib 0 (some 5) 0 (.d8 0x12))).toInstrSpec (xor_r8_m8_effect_step 0x10892f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f65 : InstrSpec 0x108933 [0x88, 0x4C, 0x24, 0x69] (StorePre 0x108933 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x69)) s (0x108933 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108933 4 1 (.sib 4 none 0 (.d8 0x69)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108933 4 1 (.sib 4 none 0 (.d8 0x69))).toInstrSpec (mov_m8_r8_effect_step 0x108933 1 (by decide) (.sib 4 none 0 (.d8 0x69)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f66 : InstrSpec 0x108937 [0x0F, 0xB6, 0x8C, 0x24, 0xAB, 0x00, 0x00, 0x00] (LoadPre 0x108937 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xab)) s (0x108937 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108937 8 1 (.sib 4 none 0 (.d32 0xab)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108937 8 1 (.sib 4 none 0 (.d32 0xab))).toInstrSpec (movzx_r32_m8_effect_step 0x108937 1 (.sib 4 none 0 (.d32 0xab)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f67 : InstrSpec 0x10893f [0x32, 0x4C, 0x28, 0x13] (LoadPre 0x10893f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x13)) s (0x10893f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10893f 4 1 (.sib 0 (some 5) 0 (.d8 0x13)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10893f 4 1 (.sib 0 (some 5) 0 (.d8 0x13))).toInstrSpec (xor_r8_m8_effect_step 0x10893f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f68 : InstrSpec 0x108943 [0x88, 0x4C, 0x24, 0x68] (StorePre 0x108943 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x108943 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108943 4 1 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108943 4 1 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m8_r8_effect_step 0x108943 1 (by decide) (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f69 : InstrSpec 0x108947 [0x0F, 0xB6, 0x8C, 0x24, 0xAC, 0x00, 0x00, 0x00] (LoadPre 0x108947 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xac)) s (0x108947 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108947 8 1 (.sib 4 none 0 (.d32 0xac)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108947 8 1 (.sib 4 none 0 (.d32 0xac))).toInstrSpec (movzx_r32_m8_effect_step 0x108947 1 (.sib 4 none 0 (.d32 0xac)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f70 : InstrSpec 0x10894f [0x32, 0x4C, 0x28, 0x14] (LoadPre 0x10894f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x14)) s (0x10894f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10894f 4 1 (.sib 0 (some 5) 0 (.d8 0x14)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10894f 4 1 (.sib 0 (some 5) 0 (.d8 0x14))).toInstrSpec (xor_r8_m8_effect_step 0x10894f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f71 : InstrSpec 0x108953 [0x88, 0x4C, 0x24, 0x67] (StorePre 0x108953 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x67)) s (0x108953 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108953 4 1 (.sib 4 none 0 (.d8 0x67)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108953 4 1 (.sib 4 none 0 (.d8 0x67))).toInstrSpec (mov_m8_r8_effect_step 0x108953 1 (by decide) (.sib 4 none 0 (.d8 0x67)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f72 : InstrSpec 0x108957 [0x0F, 0xB6, 0x8C, 0x24, 0xAD, 0x00, 0x00, 0x00] (LoadPre 0x108957 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xad)) s (0x108957 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108957 8 1 (.sib 4 none 0 (.d32 0xad)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108957 8 1 (.sib 4 none 0 (.d32 0xad))).toInstrSpec (movzx_r32_m8_effect_step 0x108957 1 (.sib 4 none 0 (.d32 0xad)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f73 : InstrSpec 0x10895f [0x32, 0x4C, 0x28, 0x15] (LoadPre 0x10895f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x15)) s (0x10895f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10895f 4 1 (.sib 0 (some 5) 0 (.d8 0x15)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10895f 4 1 (.sib 0 (some 5) 0 (.d8 0x15))).toInstrSpec (xor_r8_m8_effect_step 0x10895f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f74 : InstrSpec 0x108963 [0x88, 0x4C, 0x24, 0x66] (StorePre 0x108963 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x108963 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108963 4 1 (.sib 4 none 0 (.d8 0x66)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108963 4 1 (.sib 4 none 0 (.d8 0x66))).toInstrSpec (mov_m8_r8_effect_step 0x108963 1 (by decide) (.sib 4 none 0 (.d8 0x66)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f75 : InstrSpec 0x108967 [0x0F, 0xB6, 0x8C, 0x24, 0xAE, 0x00, 0x00, 0x00] (LoadPre 0x108967 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xae)) s (0x108967 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108967 8 1 (.sib 4 none 0 (.d32 0xae)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108967 8 1 (.sib 4 none 0 (.d32 0xae))).toInstrSpec (movzx_r32_m8_effect_step 0x108967 1 (.sib 4 none 0 (.d32 0xae)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f76 : InstrSpec 0x10896f [0x32, 0x4C, 0x28, 0x16] (LoadPre 0x10896f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x16)) s (0x10896f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10896f 4 1 (.sib 0 (some 5) 0 (.d8 0x16)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10896f 4 1 (.sib 0 (some 5) 0 (.d8 0x16))).toInstrSpec (xor_r8_m8_effect_step 0x10896f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f77 : InstrSpec 0x108973 [0x88, 0x4C, 0x24, 0x65] (StorePre 0x108973 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x65)) s (0x108973 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108973 4 1 (.sib 4 none 0 (.d8 0x65)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108973 4 1 (.sib 4 none 0 (.d8 0x65))).toInstrSpec (mov_m8_r8_effect_step 0x108973 1 (by decide) (.sib 4 none 0 (.d8 0x65)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f78 : InstrSpec 0x108977 [0x0F, 0xB6, 0x8C, 0x24, 0xAF, 0x00, 0x00, 0x00] (LoadPre 0x108977 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaf)) s (0x108977 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108977 8 1 (.sib 4 none 0 (.d32 0xaf)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108977 8 1 (.sib 4 none 0 (.d32 0xaf))).toInstrSpec (movzx_r32_m8_effect_step 0x108977 1 (.sib 4 none 0 (.d32 0xaf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f79 : InstrSpec 0x10897f [0x32, 0x4C, 0x28, 0x17] (LoadPre 0x10897f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x17)) s (0x10897f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10897f 4 1 (.sib 0 (some 5) 0 (.d8 0x17)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10897f 4 1 (.sib 0 (some 5) 0 (.d8 0x17))).toInstrSpec (xor_r8_m8_effect_step 0x10897f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x17)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f60 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 91), (1, 152), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10891f) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f61 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 91), (1, 154), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108923) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.exec (n := 156) (ρ' := [(0, 91), (1, 154), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108927) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f63 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 91), (1, 157), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10892f) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f64 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 91), (1, 159), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108933) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.exec (n := 161) (ρ' := [(0, 91), (1, 159), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108937) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f66 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 91), (1, 162), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10893f) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f67 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 91), (1, 164), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108943) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.exec (n := 166) (ρ' := [(0, 91), (1, 164), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108947) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f69 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 91), (1, 167), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10894f) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f70 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 91), (1, 169), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108953) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.exec (n := 171) (ρ' := [(0, 91), (1, 169), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108957) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f72 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 91), (1, 172), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10895f) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f73 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 91), (1, 174), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108963) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.exec (n := 176) (ρ' := [(0, 91), (1, 174), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108967) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f75 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 91), (1, 177), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10896f) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f76 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 91), (1, 179), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108973) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.exec (n := 181) (ρ' := [(0, 91), (1, 179), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108977) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f78 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 91), (1, 182), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10897f) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f79 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(0, 91), (1, 184), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108983) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1087a5_4 code

theorem rest_l1087a5_2 [Bindings] (code : CodeMap) :
    Rest (n := 120) code lifted (codeRange 0x1087a5 bytes_l1087a5) [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]
      273 0x1088a9 bytes_l1087a5_2 b_l1087a5_2 := by
  have f40 : InstrSpec 0x1088a9 [0x44, 0x32, 0x74, 0x28, 0x09] (LoadPre 0x1088a9 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x9)) s (0x1088a9 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1088a9 5 14 (.sib 0 (some 5) 0 (.d8 0x9)))
      [.gpr 14, .gpr 0, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1088a9 5 14 (.sib 0 (some 5) 0 (.d8 0x9))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1088a9 0x44 (by decide) 6 (.sib 0 (some 5) 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x1088ae [0x44, 0x88, 0x74, 0x24, 0x6E] (StorePre 0x1088ae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6e)) s (0x1088ae + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1088ae 5 14 (.sib 4 none 0 (.d8 0x6e)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1088ae 5 14 (.sib 4 none 0 (.d8 0x6e))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1088ae 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x6e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x1088b3 [0x44, 0x32, 0x7C, 0x28, 0x0A] (LoadPre 0x1088b3 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xa)) s (0x1088b3 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1088b3 5 15 (.sib 0 (some 5) 0 (.d8 0xa)))
      [.gpr 15, .gpr 0, .gpr 5] [] [.reg 15, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1088b3 5 15 (.sib 0 (some 5) 0 (.d8 0xa))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1088b3 0x44 (by decide) 7 (.sib 0 (some 5) 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f43 : InstrSpec 0x1088b8 [0x44, 0x88, 0x7C, 0x24, 0x6D] (StorePre 0x1088b8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6d)) s (0x1088b8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1088b8 5 15 (.sib 4 none 0 (.d8 0x6d)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1088b8 5 15 (.sib 4 none 0 (.d8 0x6d))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1088b8 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x6d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f44 : InstrSpec 0x1088bd [0x44, 0x32, 0x64, 0x28, 0x0B] (LoadPre 0x1088bd (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xb)) s (0x1088bd + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1088bd 5 12 (.sib 0 (some 5) 0 (.d8 0xb)))
      [.gpr 12, .gpr 0, .gpr 5] [] [.reg 12, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1088bd 5 12 (.sib 0 (some 5) 0 (.d8 0xb))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1088bd 0x44 (by decide) 4 (.sib 0 (some 5) 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f45 : InstrSpec 0x1088c2 [0x44, 0x88, 0x64, 0x24, 0x6C] (StorePre 0x1088c2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x1088c2 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1088c2 5 12 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1088c2 5 12 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1088c2 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f46 : InstrSpec 0x1088c7 [0x44, 0x32, 0x6C, 0x28, 0x0C] (LoadPre 0x1088c7 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xc)) s (0x1088c7 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1088c7 5 13 (.sib 0 (some 5) 0 (.d8 0xc)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1088c7 5 13 (.sib 0 (some 5) 0 (.d8 0xc))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1088c7 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f47 : InstrSpec 0x1088cc [0x44, 0x88, 0x6C, 0x24, 0x6B] (StorePre 0x1088cc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6b)) s (0x1088cc + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1088cc 5 13 (.sib 4 none 0 (.d8 0x6b)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1088cc 5 13 (.sib 4 none 0 (.d8 0x6b))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1088cc 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x6b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x1088d1 [0x0F, 0xB6, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x1088d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1088d1 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1088d1 8 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1088d1 8 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (movzx_r32_m8_effect_step 0x1088d1 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f49 : InstrSpec 0x1088d9 [0x32, 0x4C, 0x28, 0x0D] (LoadPre 0x1088d9 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xd)) s (0x1088d9 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1088d9 4 1 (.sib 0 (some 5) 0 (.d8 0xd)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1088d9 4 1 (.sib 0 (some 5) 0 (.d8 0xd))).toInstrSpec (xor_r8_m8_effect_step 0x1088d9 1 (by decide) (.sib 0 (some 5) 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f50 : InstrSpec 0x1088dd [0x88, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x1088dd 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1088dd + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1088dd 7 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1088dd 7 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m8_r8_effect_step 0x1088dd 1 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f51 : InstrSpec 0x1088e4 [0x0F, 0xB6, 0x4C, 0x24, 0x78] (LoadPre 0x1088e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1088e4 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1088e4 5 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1088e4 5 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (movzx_r32_m8_effect_step 0x1088e4 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f52 : InstrSpec 0x1088e9 [0x32, 0x4C, 0x28, 0x0E] (LoadPre 0x1088e9 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xe)) s (0x1088e9 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1088e9 4 1 (.sib 0 (some 5) 0 (.d8 0xe)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1088e9 4 1 (.sib 0 (some 5) 0 (.d8 0xe))).toInstrSpec (xor_r8_m8_effect_step 0x1088e9 1 (by decide) (.sib 0 (some 5) 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f53 : InstrSpec 0x1088ed [0x88, 0x4C, 0x24, 0x78] (StorePre 0x1088ed 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1088ed + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1088ed 4 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1088ed 4 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m8_r8_effect_step 0x1088ed 1 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x1088f1 [0x0F, 0xB6, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x1088f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1088f1 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1088f1 8 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1088f1 8 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (movzx_r32_m8_effect_step 0x1088f1 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f55 : InstrSpec 0x1088f9 [0x32, 0x4C, 0x28, 0x0F] (LoadPre 0x1088f9 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xf)) s (0x1088f9 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1088f9 4 1 (.sib 0 (some 5) 0 (.d8 0xf)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1088f9 4 1 (.sib 0 (some 5) 0 (.d8 0xf))).toInstrSpec (xor_r8_m8_effect_step 0x1088f9 1 (by decide) (.sib 0 (some 5) 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f56 : InstrSpec 0x1088fd [0x88, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1088fd 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1088fd + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1088fd 7 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1088fd 7 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m8_r8_effect_step 0x1088fd 1 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f57 : InstrSpec 0x108904 [0x0F, 0xB6, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x108904 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x108904 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108904 8 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108904 8 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (movzx_r32_m8_effect_step 0x108904 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f58 : InstrSpec 0x10890c [0x32, 0x4C, 0x28, 0x10] (LoadPre 0x10890c (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x10)) s (0x10890c + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10890c 4 1 (.sib 0 (some 5) 0 (.d8 0x10)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10890c 4 1 (.sib 0 (some 5) 0 (.d8 0x10))).toInstrSpec (xor_r8_m8_effect_step 0x10890c 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f59 : InstrSpec 0x108910 [0x88, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x108910 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x108910 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x108910 7 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108910 7 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m8_r8_effect_step 0x108910 1 (by decide) (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f40 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 120), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088ae) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.exec (n := 122) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 120), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088b3) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f42 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088b8) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.exec (n := 125) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088bd) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f44 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 77), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088c2) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.exec (n := 128) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 77), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088c7) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f46 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088cc) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.exec (n := 131) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088d1) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f48 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 91), (1, 132), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088d9) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f49 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 91), (1, 134), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088dd) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.exec (n := 136) (ρ' := [(0, 91), (1, 134), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088e4) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f51 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 91), (1, 137), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088e9) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f52 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 91), (1, 139), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088ed) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.exec (n := 141) (ρ' := [(0, 91), (1, 139), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088f1) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f54 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 91), (1, 142), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088f9) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f55 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 91), (1, 144), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088fd) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.exec (n := 146) (ρ' := [(0, 91), (1, 144), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108904) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f57 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 91), (1, 147), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10890c) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f58 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 91), (1, 149), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108910) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.exec (n := 151) (ρ' := [(0, 91), (1, 149), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108917) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1087a5_3 code

theorem rest_l1087a5_1 [Bindings] (code : CodeMap) :
    Rest (n := 90) code lifted (codeRange 0x1087a5 bytes_l1087a5) [(0, 88), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]
      293 0x108847 bytes_l1087a5_1 b_l1087a5_1 := by
  have f20 : InstrSpec 0x108847 [0x88, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x108847 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x108847 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x108847 7 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108847 7 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m8_r8_effect_step 0x108847 0 (by decide) (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x10884e [0x48, 0x8B, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00] (LoadPre 0x10884e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10884e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10884e 0 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10884e 0 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x10884e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x108856 [0x32, 0x0C, 0x28] (LoadPre 0x108856 (fun s => AddrMode.addr (.sib 0 (some 5) 0 .none) s (0x108856 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x108856 3 1 (.sib 0 (some 5) 0 .none))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108856 3 1 (.sib 0 (some 5) 0 .none)).toInstrSpec (xor_r8_m8_effect_step 0x108856 1 (by decide) (.sib 0 (some 5) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x108859 [0x88, 0x4C, 0x24, 0x77] (StorePre 0x108859 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x77)) s (0x108859 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108859 4 1 (.sib 4 none 0 (.d8 0x77)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108859 4 1 (.sib 4 none 0 (.d8 0x77))).toInstrSpec (mov_m8_r8_effect_step 0x108859 1 (by decide) (.sib 4 none 0 (.d8 0x77)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x10885d [0x32, 0x54, 0x28, 0x01] (LoadPre 0x10885d (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1)) s (0x10885d + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10885d 4 2 (.sib 0 (some 5) 0 (.d8 0x1)))
      [.gpr 2, .gpr 0, .gpr 5] [] [.reg 2, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10885d 4 2 (.sib 0 (some 5) 0 (.d8 0x1))).toInstrSpec (xor_r8_m8_effect_step 0x10885d 2 (by decide) (.sib 0 (some 5) 0 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x108861 [0x88, 0x54, 0x24, 0x76] (StorePre 0x108861 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x108861 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108861 4 2 (.sib 4 none 0 (.d8 0x76)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108861 4 2 (.sib 4 none 0 (.d8 0x76))).toInstrSpec (mov_m8_r8_effect_step 0x108861 2 (by decide) (.sib 4 none 0 (.d8 0x76)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x108865 [0x40, 0x32, 0x74, 0x28, 0x02] (LoadPre 0x108865 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2)) s (0x108865 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108865 5 6 (.sib 0 (some 5) 0 (.d8 0x2)))
      [.gpr 6, .gpr 0, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108865 5 6 (.sib 0 (some 5) 0 (.d8 0x2))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108865 0x40 (by decide) 6 (.sib 0 (some 5) 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x10886a [0x40, 0x88, 0x74, 0x24, 0x75] (StorePre 0x10886a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x75)) s (0x10886a + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10886a 5 6 (.sib 4 none 0 (.d8 0x75)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10886a 5 6 (.sib 4 none 0 (.d8 0x75))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10886a 0x40 (by decide) 6 (.sib 4 none 0 (.d8 0x75)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x10886f [0x40, 0x32, 0x7C, 0x28, 0x03] (LoadPre 0x10886f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3)) s (0x10886f + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x10886f 5 7 (.sib 0 (some 5) 0 (.d8 0x3)))
      [.gpr 7, .gpr 0, .gpr 5] [] [.reg 7, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10886f 5 7 (.sib 0 (some 5) 0 (.d8 0x3))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10886f 0x40 (by decide) 7 (.sib 0 (some 5) 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x108874 [0x40, 0x88, 0x7C, 0x24, 0x74] (StorePre 0x108874 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x108874 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108874 5 7 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108874 5 7 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108874 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x108879 [0x44, 0x32, 0x44, 0x28, 0x04] (LoadPre 0x108879 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x4)) s (0x108879 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108879 5 8 (.sib 0 (some 5) 0 (.d8 0x4)))
      [.gpr 8, .gpr 0, .gpr 5] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108879 5 8 (.sib 0 (some 5) 0 (.d8 0x4))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108879 0x44 (by decide) 0 (.sib 0 (some 5) 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x10887e [0x44, 0x88, 0x44, 0x24, 0x73] (StorePre 0x10887e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x73)) s (0x10887e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10887e 5 8 (.sib 4 none 0 (.d8 0x73)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10887e 5 8 (.sib 4 none 0 (.d8 0x73))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10887e 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x73)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x108883 [0x44, 0x32, 0x4C, 0x28, 0x05] (LoadPre 0x108883 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x5)) s (0x108883 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108883 5 9 (.sib 0 (some 5) 0 (.d8 0x5)))
      [.gpr 9, .gpr 0, .gpr 5] [] [.reg 9, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108883 5 9 (.sib 0 (some 5) 0 (.d8 0x5))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108883 0x44 (by decide) 1 (.sib 0 (some 5) 0 (.d8 0x5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x108888 [0x44, 0x88, 0x4C, 0x24, 0x72] (StorePre 0x108888 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x108888 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108888 5 9 (.sib 4 none 0 (.d8 0x72)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108888 5 9 (.sib 4 none 0 (.d8 0x72))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108888 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x72)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x10888d [0x44, 0x32, 0x54, 0x28, 0x06] (LoadPre 0x10888d (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x6)) s (0x10888d + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x10888d 5 10 (.sib 0 (some 5) 0 (.d8 0x6)))
      [.gpr 10, .gpr 0, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10888d 5 10 (.sib 0 (some 5) 0 (.d8 0x6))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10888d 0x44 (by decide) 2 (.sib 0 (some 5) 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x108892 [0x44, 0x88, 0x54, 0x24, 0x71] (StorePre 0x108892 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x71)) s (0x108892 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108892 5 10 (.sib 4 none 0 (.d8 0x71)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108892 5 10 (.sib 4 none 0 (.d8 0x71))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108892 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x71)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x108897 [0x44, 0x32, 0x5C, 0x28, 0x07] (LoadPre 0x108897 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x7)) s (0x108897 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108897 5 11 (.sib 0 (some 5) 0 (.d8 0x7)))
      [.gpr 11, .gpr 0, .gpr 5] [] [.reg 11, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108897 5 11 (.sib 0 (some 5) 0 (.d8 0x7))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108897 0x44 (by decide) 3 (.sib 0 (some 5) 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x10889c [0x44, 0x88, 0x5C, 0x24, 0x70] (StorePre 0x10889c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10889c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10889c 5 11 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10889c 5 11 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10889c 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x1088a1 [0x32, 0x5C, 0x28, 0x08] (LoadPre 0x1088a1 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x8)) s (0x1088a1 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1088a1 4 3 (.sib 0 (some 5) 0 (.d8 0x8)))
      [.gpr 3, .gpr 0, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1088a1 4 3 (.sib 0 (some 5) 0 (.d8 0x8))).toInstrSpec (xor_r8_m8_effect_step 0x1088a1 3 (by decide) (.sib 0 (some 5) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x1088a5 [0x88, 0x5C, 0x24, 0x6F] (StorePre 0x1088a5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6f)) s (0x1088a5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1088a5 4 3 (.sib 4 none 0 (.d8 0x6f)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1088a5 4 3 (.sib 4 none 0 (.d8 0x6f))).toInstrSpec (mov_m8_r8_effect_step 0x1088a5 3 (by decide) (.sib 4 none 0 (.d8 0x6f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 88), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10884e) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 91), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108856) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 91), (1, 93), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108859) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 91), (1, 93), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10885d) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f24 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108861) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108865) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f26 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10886a) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10886f) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f28 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108874) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108879) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f30 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10887e) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108883) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f32 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108888) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.exec (n := 110) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10888d) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f34 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108892) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.exec (n := 113) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108897) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f36 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10889c) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.exec (n := 116) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088a1) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f38 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088a5) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.exec (n := 119) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088a9) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1087a5_2 code

theorem rest_l1087a5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1087a5 bytes_l1087a5) (entryMap (live .l1087a5))
      313 0x1087a5 bytes_l1087a5 b_l1087a5 := by
  have f0 : InstrSpec 0x1087a5 [0x0F, 0xB6, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x1087a5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1087a5 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1087a5 8 1 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1087a5 8 1 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (movzx_r32_m8_effect_step 0x1087a5 1 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1087ad [0x0F, 0xB6, 0x94, 0x24, 0x99, 0x00, 0x00, 0x00] (LoadPre 0x1087ad (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x99)) s (0x1087ad + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1087ad 8 2 (.sib 4 none 0 (.d32 0x99)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1087ad 8 2 (.sib 4 none 0 (.d32 0x99))).toInstrSpec (movzx_r32_m8_effect_step 0x1087ad 2 (.sib 4 none 0 (.d32 0x99)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1087b5 [0x0F, 0xB6, 0xB4, 0x24, 0x9A, 0x00, 0x00, 0x00] (LoadPre 0x1087b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9a)) s (0x1087b5 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1087b5 8 6 (.sib 4 none 0 (.d32 0x9a)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x1087b5 8 6 (.sib 4 none 0 (.d32 0x9a))).toInstrSpec (movzx_r32_m8_effect_step 0x1087b5 6 (.sib 4 none 0 (.d32 0x9a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1087bd [0x0F, 0xB6, 0xBC, 0x24, 0x9B, 0x00, 0x00, 0x00] (LoadPre 0x1087bd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9b)) s (0x1087bd + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1087bd 8 7 (.sib 4 none 0 (.d32 0x9b)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x1087bd 8 7 (.sib 4 none 0 (.d32 0x9b))).toInstrSpec (movzx_r32_m8_effect_step 0x1087bd 7 (.sib 4 none 0 (.d32 0x9b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1087c5 [0x44, 0x0F, 0xB6, 0x84, 0x24, 0x9C, 0x00, 0x00, 0x00] (LoadPre 0x1087c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x1087c5 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1087c5 9 8 (.sib 4 none 0 (.d32 0x9c)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x1087c5 9 8 (.sib 4 none 0 (.d32 0x9c))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1087c5 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0x9c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1087ce [0x44, 0x0F, 0xB6, 0x8C, 0x24, 0x9D, 0x00, 0x00, 0x00] (LoadPre 0x1087ce (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9d)) s (0x1087ce + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1087ce 9 9 (.sib 4 none 0 (.d32 0x9d)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x1087ce 9 9 (.sib 4 none 0 (.d32 0x9d))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1087ce 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0x9d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1087d7 [0x44, 0x0F, 0xB6, 0x94, 0x24, 0x9E, 0x00, 0x00, 0x00] (LoadPre 0x1087d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9e)) s (0x1087d7 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1087d7 9 10 (.sib 4 none 0 (.d32 0x9e)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x1087d7 9 10 (.sib 4 none 0 (.d32 0x9e))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1087d7 0x44 (by decide) 2 (.sib 4 none 0 (.d32 0x9e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1087e0 [0x44, 0x0F, 0xB6, 0x9C, 0x24, 0x9F, 0x00, 0x00, 0x00] (LoadPre 0x1087e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x1087e0 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1087e0 9 11 (.sib 4 none 0 (.d32 0x9f)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x1087e0 9 11 (.sib 4 none 0 (.d32 0x9f))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1087e0 0x44 (by decide) 3 (.sib 4 none 0 (.d32 0x9f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1087e9 [0x0F, 0xB6, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x1087e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1087e9 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1087e9 8 3 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x1087e9 8 3 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (movzx_r32_m8_effect_step 0x1087e9 3 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1087f1 [0x44, 0x0F, 0xB6, 0xB4, 0x24, 0xA1, 0x00, 0x00, 0x00] (LoadPre 0x1087f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa1)) s (0x1087f1 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1087f1 9 14 (.sib 4 none 0 (.d32 0xa1)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x1087f1 9 14 (.sib 4 none 0 (.d32 0xa1))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1087f1 0x44 (by decide) 6 (.sib 4 none 0 (.d32 0xa1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1087fa [0x44, 0x0F, 0xB6, 0xBC, 0x24, 0xA2, 0x00, 0x00, 0x00] (LoadPre 0x1087fa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa2)) s (0x1087fa + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1087fa 9 15 (.sib 4 none 0 (.d32 0xa2)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x1087fa 9 15 (.sib 4 none 0 (.d32 0xa2))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1087fa 0x44 (by decide) 7 (.sib 4 none 0 (.d32 0xa2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x108803 [0x44, 0x0F, 0xB6, 0xA4, 0x24, 0xA3, 0x00, 0x00, 0x00] (LoadPre 0x108803 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa3)) s (0x108803 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108803 9 12 (.sib 4 none 0 (.d32 0xa3)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x108803 9 12 (.sib 4 none 0 (.d32 0xa3))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108803 0x44 (by decide) 4 (.sib 4 none 0 (.d32 0xa3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x10880c [0x44, 0x0F, 0xB6, 0xAC, 0x24, 0xA4, 0x00, 0x00, 0x00] (LoadPre 0x10880c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x10880c + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x10880c 9 13 (.sib 4 none 0 (.d32 0xa4)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x10880c 9 13 (.sib 4 none 0 (.d32 0xa4))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10880c 0x44 (by decide) 5 (.sib 4 none 0 (.d32 0xa4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x108815 [0x0F, 0xB6, 0x84, 0x24, 0xA5, 0x00, 0x00, 0x00] (LoadPre 0x108815 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa5)) s (0x108815 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108815 8 0 (.sib 4 none 0 (.d32 0xa5)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x108815 8 0 (.sib 4 none 0 (.d32 0xa5))).toInstrSpec (movzx_r32_m8_effect_step 0x108815 0 (.sib 4 none 0 (.d32 0xa5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10881d [0x88, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x10881d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10881d + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10881d 7 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10881d 7 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m8_r8_effect_step 0x10881d 0 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x108824 [0x0F, 0xB6, 0x84, 0x24, 0xA6, 0x00, 0x00, 0x00] (LoadPre 0x108824 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa6)) s (0x108824 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108824 8 0 (.sib 4 none 0 (.d32 0xa6)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x108824 8 0 (.sib 4 none 0 (.d32 0xa6))).toInstrSpec (movzx_r32_m8_effect_step 0x108824 0 (.sib 4 none 0 (.d32 0xa6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10882c [0x88, 0x44, 0x24, 0x78] (StorePre 0x10882c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10882c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10882c 4 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10882c 4 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m8_r8_effect_step 0x10882c 0 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x108830 [0x0F, 0xB6, 0x84, 0x24, 0xA7, 0x00, 0x00, 0x00] (LoadPre 0x108830 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa7)) s (0x108830 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108830 8 0 (.sib 4 none 0 (.d32 0xa7)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x108830 8 0 (.sib 4 none 0 (.d32 0xa7))).toInstrSpec (movzx_r32_m8_effect_step 0x108830 0 (.sib 4 none 0 (.d32 0xa7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x108838 [0x88, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x108838 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x108838 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x108838 7 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108838 7 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m8_r8_effect_step 0x108838 0 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x10883f [0x0F, 0xB6, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x10883f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10883f + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10883f 8 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10883f 8 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (movzx_r32_m8_effect_step 0x10883f 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087ad) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 55), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087b5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (2, 55), (4, 4), (5, 5), (6, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087bd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 53), (2, 55), (4, 4), (5, 5), (6, 57), (7, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087c5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 53), (2, 55), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087ce) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 53), (2, 55), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087d7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 53), (2, 55), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087e0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 53), (2, 55), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087e9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087f1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (14, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087fa) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108803) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10880c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108815) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10881d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 79), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108824) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 82), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10882c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 82), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108830) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108838) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 85), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10883f) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 88), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108847) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1087a5_1 code

theorem block_l1087a5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1087a5 :=
  Rest.liftedBlock (rest_l1087a5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1087a5 x hx)

theorem rest_l108e98_2 [Bindings] (code : CodeMap) :
    Rest (n := 108) code lifted (codeRange 0x108e98 bytes_l108e98) [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x108f8b bytes_l108e98_2 b_l108e98_2 := by
  have f40 : InstrSpec 0x108f8b [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108f8b) (movR32Imm32Effect 0x108f8b 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x108f8b 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x108f8b 0xbe (by decide) 0x8) pre_rip
  have f41 : InstrSpec 0x108f90 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x108f90) (leaR64Effect 0x108f90 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x108f90 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x108f90 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x108f95 [0x48, 0x8D, 0x94, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x108f95) (leaR64Effect 0x108f95 2 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x108f95 2 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x108f95 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x108f9d [0xE8, 0xEE, 0x16, 0x00, 0x00] (PushPre 0x108f9d 5) (callEffect (fun _ => 0x10a690) 0x108fa2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x108f9d 0x10a690 0x108fa2).toInstrSpec (call_rel32_effect_step 0x108f9d 0x16ee (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f40 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 108), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f90) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f41 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 108), (7, 110), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f95) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f42 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 93), (1, 57), (2, 112), (3, 3), (4, 4), (5, 5), (6, 108), (7, 110), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f9d) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f43 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 93), (1, 57), (2, 112), (3, 3), (4, 114), (5, 5), (6, 108), (7, 110), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a690) f43 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 116) (by decide) (by decide) rfl rfl

theorem rest_l108e98_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x108e98 bytes_l108e98) [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      24 0x108f03 bytes_l108e98_1 b_l108e98_1 := by
  have f20 : InstrSpec 0x108f03 [0x89, 0x94, 0x24, 0x24, 0x01, 0x00, 0x00] (StorePre 0x108f03 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x124)) s (0x108f03 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108f03 2 (.sib 4 none 0 (.d32 0x124)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x108f03 2 (.sib 4 none 0 (.d32 0x124))).toInstrSpec (mov_m32_r32_low_effect_step 0x108f03 2 (.sib 4 none 0 (.d32 0x124)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x108f0a [0x89, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00] (StorePre 0x108f0a 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x108f0a + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108f0a 6 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x108f0a 6 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_m32_r32_low_effect_step 0x108f0a 6 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x108f11 [0x44, 0x89, 0x84, 0x24, 0x2C, 0x01, 0x00, 0x00] (StorePre 0x108f11 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x12c)) s (0x108f11 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x108f11 8 (.sib 4 none 0 (.d32 0x12c)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x108f11 8 (.sib 4 none 0 (.d32 0x12c))).toInstrSpec (mov_m32_r32_effect_step 0x108f11 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0x12c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x108f19 [0x01, 0xC7] (fun s => s.RIP = 0x108f19) (addR32R32Effect 0x108f19 2 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (addR32R32Effect_footprint 0x108f19 2 7 0).toInstrSpec (add_r32_r32_effect_step 0x108f19 0xc7 (by decide)) pre_rip
  have f24 : InstrSpec 0x108f1b [0x83, 0xC7, 0x03] (fun s => s.RIP = 0x108f1b) (addR32Imm8Effect 0x108f1b 3 7 0x3)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR32Imm8Effect_footprint 0x108f1b 3 7 0x3).toInstrSpec (add_r32_imm8_effect_step 0x108f1b 0xc7 0x3 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x108f1e [0x0F, 0xCF] (fun s => s.RIP = 0x108f1e) (bswapR32Effect 0x108f1e 2 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (bswapR32Effect_footprint 0x108f1e 2 7).toInstrSpec (bswap_r32_effect_step 0x108f1e 0xcf (by decide)) pre_rip
  have f26 : InstrSpec 0x108f20 [0x83, 0xC0, 0x04] (fun s => s.RIP = 0x108f20) (addR32Imm8Effect 0x108f20 3 0 0x4)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32Imm8Effect_footprint 0x108f20 3 0 0x4).toInstrSpec (add_r32_imm8_effect_step 0x108f20 0xc0 0x4 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x108f23 [0x41, 0x89, 0x41, 0x10] (StorePre 0x108f23 4 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x108f23 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x108f23 0 (.base 9 (.d8 0x10)))
      [.gpr 0, .gpr 9] [] [.rip] :=
    (movM32R32Effect_footprint 0x108f23 0 (.base 9 (.d8 0x10))).toInstrSpec (mov_m32_r32_effect_step 0x108f23 0x41 (by decide) 0 (.base 9 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x108f27 [0x89, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00] (StorePre 0x108f27 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x108f27 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108f27 1 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x108f27 1 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_m32_r32_low_effect_step 0x108f27 1 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x108f2e [0x89, 0x94, 0x24, 0x34, 0x01, 0x00, 0x00] (StorePre 0x108f2e 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x134)) s (0x108f2e + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108f2e 2 (.sib 4 none 0 (.d32 0x134)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x108f2e 2 (.sib 4 none 0 (.d32 0x134))).toInstrSpec (mov_m32_r32_low_effect_step 0x108f2e 2 (.sib 4 none 0 (.d32 0x134)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x108f35 [0x89, 0xB4, 0x24, 0x38, 0x01, 0x00, 0x00] (StorePre 0x108f35 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x108f35 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108f35 6 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x108f35 6 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_m32_r32_low_effect_step 0x108f35 6 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x108f3c [0x89, 0xBC, 0x24, 0x3C, 0x01, 0x00, 0x00] (StorePre 0x108f3c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x13c)) s (0x108f3c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108f3c 7 (.sib 4 none 0 (.d32 0x13c)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x108f3c 7 (.sib 4 none 0 (.d32 0x13c))).toInstrSpec (mov_m32_r32_low_effect_step 0x108f3c 7 (.sib 4 none 0 (.d32 0x13c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x108f43 [0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108f43 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x108f43 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f43 (.sib 4 none 0 (.d8 0x40)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108f43 (.sib 4 none 0 (.d8 0x40)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108f43 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x108f4c [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108f4c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x108f4c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f4c (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108f4c (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108f4c 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x108f55 [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108f55 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108f55 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f55 (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108f55 (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108f55 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x108f5e [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108f5e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x108f5e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f5e (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108f5e (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108f5e 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x108f67 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108f67 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x108f67 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f67 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108f67 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108f67 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x108f70 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108f70 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x108f70 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f70 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108f70 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108f70 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x108f79 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108f79 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108f79 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f79 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108f79 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108f79 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x108f82 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108f82 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108f82 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f82 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108f82 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108f82 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f0a) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f11) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f19) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f23 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 87), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f1b) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f24 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 89), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f1e) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f25 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f20) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f26 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f23) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f27) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f2e) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f35) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f3c) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f43) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f4c) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f55) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.exec (n := 102) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f5e) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 103) (RestInside.exec (n := 103) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f67) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f70) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.exec (n := 105) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f79) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f82) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f8b) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l108e98_2 code

theorem rest_l108e98 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108e98 bytes_l108e98) (entryMap (live .l108e98))
      44 0x108e98 bytes_l108e98 b_l108e98 := by
  have f0 : InstrSpec 0x108e98 [0x41, 0x8B, 0x41, 0x10] (LoadPre 0x108e98 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x108e98 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x108e98 0 (.base 9 (.d8 0x10)))
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR32M32Effect_footprint 0x108e98 0 (.base 9 (.d8 0x10))).toInstrSpec (mov_r32_m32_effect_step 0x108e98 0x41 (by decide) 0 (.base 9 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x108e9c [0x41, 0x8B, 0x79, 0x0C] (LoadPre 0x108e9c (fun s => AddrMode.addr (.base 9 (.d8 0xc)) s (0x108e9c + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x108e9c 7 (.base 9 (.d8 0xc)))
      [.gpr 9] [] [.reg 7, .rip] :=
    (movR32M32Effect_footprint 0x108e9c 7 (.base 9 (.d8 0xc))).toInstrSpec (mov_r32_m32_effect_step 0x108e9c 0x41 (by decide) 7 (.base 9 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x108ea0 [0x41, 0x8B, 0x09] (LoadPre 0x108ea0 (fun s => AddrMode.addr (.base 9 .none) s (0x108ea0 + BitVec.ofNat 64 3)) 4) (movR32M32Effect 0x108ea0 1 (.base 9 .none))
      [.gpr 9] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x108ea0 1 (.base 9 .none)).toInstrSpec (mov_r32_m32_effect_step 0x108ea0 0x41 (by decide) 1 (.base 9 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x108ea3 [0x41, 0x8B, 0x51, 0x04] (LoadPre 0x108ea3 (fun s => AddrMode.addr (.base 9 (.d8 0x4)) s (0x108ea3 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x108ea3 2 (.base 9 (.d8 0x4)))
      [.gpr 9] [] [.reg 2, .rip] :=
    (movR32M32Effect_footprint 0x108ea3 2 (.base 9 (.d8 0x4))).toInstrSpec (mov_r32_m32_effect_step 0x108ea3 0x41 (by decide) 2 (.base 9 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x108ea7 [0x41, 0x8B, 0x71, 0x08] (LoadPre 0x108ea7 (fun s => AddrMode.addr (.base 9 (.d8 0x8)) s (0x108ea7 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x108ea7 6 (.base 9 (.d8 0x8)))
      [.gpr 9] [] [.reg 6, .rip] :=
    (movR32M32Effect_footprint 0x108ea7 6 (.base 9 (.d8 0x8))).toInstrSpec (mov_r32_m32_effect_step 0x108ea7 0x41 (by decide) 6 (.base 9 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x108eab [0x44, 0x8D, 0x04, 0x07] (fun s => s.RIP = 0x108eab) (leaR32Effect 0x108eab 4 8 (.sib 7 (some 0) 0 .none))
      [.gpr 7, .gpr 0] [] [.reg 8, .rip] :=
    (leaR32Effect_footprint 0x108eab 4 8 (.sib 7 (some 0) 0 .none)).toInstrSpec (lea_r32_rex_effect_step 0x108eab 0x44 (by decide) 0 (.sib 7 (some 0) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x108eaf [0x41, 0x0F, 0xC8] (fun s => s.RIP = 0x108eaf) (bswapR32Effect 0x108eaf 3 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (bswapR32Effect_footprint 0x108eaf 3 8).toInstrSpec (bswap_r32_rex_effect_step 0x108eaf 0x41 (by decide) 0xc8 (by decide)) pre_rip
  have f7 : InstrSpec 0x108eb2 [0x89, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x108eb2 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x108eb2 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108eb2 1 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x108eb2 1 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m32_r32_low_effect_step 0x108eb2 1 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x108eb9 [0x89, 0x94, 0x24, 0x04, 0x01, 0x00, 0x00] (StorePre 0x108eb9 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x104)) s (0x108eb9 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108eb9 2 (.sib 4 none 0 (.d32 0x104)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x108eb9 2 (.sib 4 none 0 (.d32 0x104))).toInstrSpec (mov_m32_r32_low_effect_step 0x108eb9 2 (.sib 4 none 0 (.d32 0x104)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x108ec0 [0x89, 0xB4, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x108ec0 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x108ec0 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108ec0 6 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x108ec0 6 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m32_r32_low_effect_step 0x108ec0 6 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x108ec7 [0x44, 0x89, 0x84, 0x24, 0x0C, 0x01, 0x00, 0x00] (StorePre 0x108ec7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10c)) s (0x108ec7 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x108ec7 8 (.sib 4 none 0 (.d32 0x10c)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x108ec7 8 (.sib 4 none 0 (.d32 0x10c))).toInstrSpec (mov_m32_r32_effect_step 0x108ec7 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0x10c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x108ecf [0x44, 0x8D, 0x44, 0x07, 0x01] (fun s => s.RIP = 0x108ecf) (leaR32Effect 0x108ecf 5 8 (.sib 7 (some 0) 0 (.d8 0x1)))
      [.gpr 7, .gpr 0] [] [.reg 8, .rip] :=
    (leaR32Effect_footprint 0x108ecf 5 8 (.sib 7 (some 0) 0 (.d8 0x1))).toInstrSpec (lea_r32_rex_effect_step 0x108ecf 0x44 (by decide) 0 (.sib 7 (some 0) 0 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x108ed4 [0x41, 0x0F, 0xC8] (fun s => s.RIP = 0x108ed4) (bswapR32Effect 0x108ed4 3 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (bswapR32Effect_footprint 0x108ed4 3 8).toInstrSpec (bswap_r32_rex_effect_step 0x108ed4 0x41 (by decide) 0xc8 (by decide)) pre_rip
  have f13 : InstrSpec 0x108ed7 [0x89, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x108ed7 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x108ed7 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108ed7 1 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x108ed7 1 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m32_r32_low_effect_step 0x108ed7 1 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x108ede [0x89, 0x94, 0x24, 0x14, 0x01, 0x00, 0x00] (StorePre 0x108ede 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x114)) s (0x108ede + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108ede 2 (.sib 4 none 0 (.d32 0x114)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x108ede 2 (.sib 4 none 0 (.d32 0x114))).toInstrSpec (mov_m32_r32_low_effect_step 0x108ede 2 (.sib 4 none 0 (.d32 0x114)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x108ee5 [0x89, 0xB4, 0x24, 0x18, 0x01, 0x00, 0x00] (StorePre 0x108ee5 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x108ee5 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108ee5 6 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x108ee5 6 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_m32_r32_low_effect_step 0x108ee5 6 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x108eec [0x44, 0x89, 0x84, 0x24, 0x1C, 0x01, 0x00, 0x00] (StorePre 0x108eec 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11c)) s (0x108eec + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x108eec 8 (.sib 4 none 0 (.d32 0x11c)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x108eec 8 (.sib 4 none 0 (.d32 0x11c))).toInstrSpec (mov_m32_r32_effect_step 0x108eec 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0x11c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x108ef4 [0x44, 0x8D, 0x44, 0x07, 0x02] (fun s => s.RIP = 0x108ef4) (leaR32Effect 0x108ef4 5 8 (.sib 7 (some 0) 0 (.d8 0x2)))
      [.gpr 7, .gpr 0] [] [.reg 8, .rip] :=
    (leaR32Effect_footprint 0x108ef4 5 8 (.sib 7 (some 0) 0 (.d8 0x2))).toInstrSpec (lea_r32_rex_effect_step 0x108ef4 0x44 (by decide) 0 (.sib 7 (some 0) 0 (.d8 0x2)) (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x108ef9 [0x41, 0x0F, 0xC8] (fun s => s.RIP = 0x108ef9) (bswapR32Effect 0x108ef9 3 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (bswapR32Effect_footprint 0x108ef9 3 8).toInstrSpec (bswap_r32_rex_effect_step 0x108ef9 0x41 (by decide) 0xc8 (by decide)) pre_rip
  have f19 : InstrSpec 0x108efc [0x89, 0x8C, 0x24, 0x20, 0x01, 0x00, 0x00] (StorePre 0x108efc 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x108efc + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108efc 1 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x108efc 1 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_m32_r32_low_effect_step 0x108efc 1 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e9c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ea0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ea3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ea7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108eab) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108eaf) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 65), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108eb2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 65), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108eb9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 65), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ec0) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 65), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ec7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 65), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ecf) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 71), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ed4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 73), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ed7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 73), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ede) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 73), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ee5) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 73), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108eec) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 73), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ef4) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 79), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ef9) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108efc) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f03) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l108e98_1 code

theorem block_l108e98 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108e98 :=
  Rest.liftedBlock (rest_l108e98 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108e98 x hx)

theorem rest_l108fa2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108fa2 bytes_l108fa2) (entryMap (live .l108fa2))
      17 0x108fa2 bytes_l108fa2 b_l108fa2 := by
  have f0 : InstrSpec 0x108fa2 [0x48, 0x8B, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00] (LoadPre 0x108fa2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x108fa2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108fa2 0 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108fa2 0 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (mov_r64_m64_effect_step 0x108fa2 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x108faa [0x48, 0x31, 0x44, 0x24, 0x08] (StorePre 0x108faa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108faa + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108faa 5 64 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x108faa 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (xor_m64_r64_effect_step 0x108faa 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x108faf [0x48, 0x8B, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00] (LoadPre 0x108faf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x108faf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108faf 0 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108faf 0 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (mov_r64_m64_effect_step 0x108faf 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x108fb7 [0x48, 0x31, 0x44, 0x24, 0x10] (StorePre 0x108fb7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108fb7 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108fb7 5 64 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x108fb7 5 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (xor_m64_r64_effect_step 0x108fb7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x108fbc [0x48, 0x8B, 0x84, 0x24, 0x68, 0x01, 0x00, 0x00] (LoadPre 0x108fbc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x108fbc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108fbc 0 (.sib 4 none 0 (.d32 0x168)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108fbc 0 (.sib 4 none 0 (.d32 0x168))).toInstrSpec (mov_r64_m64_effect_step 0x108fbc 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x168)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x108fc4 [0x48, 0x31, 0x44, 0x24, 0x18] (StorePre 0x108fc4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x108fc4 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108fc4 5 64 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x108fc4 5 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (xor_m64_r64_effect_step 0x108fc4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x108fc9 [0x48, 0x8B, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00] (LoadPre 0x108fc9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x108fc9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108fc9 0 (.sib 4 none 0 (.d32 0x170)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108fc9 0 (.sib 4 none 0 (.d32 0x170))).toInstrSpec (mov_r64_m64_effect_step 0x108fc9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x108fd1 [0x48, 0x31, 0x44, 0x24, 0x20] (StorePre 0x108fd1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x108fd1 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108fd1 5 64 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x108fd1 5 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (xor_m64_r64_effect_step 0x108fd1 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x108fd6 [0x48, 0x8B, 0x84, 0x24, 0x78, 0x01, 0x00, 0x00] (LoadPre 0x108fd6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x108fd6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108fd6 0 (.sib 4 none 0 (.d32 0x178)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108fd6 0 (.sib 4 none 0 (.d32 0x178))).toInstrSpec (mov_r64_m64_effect_step 0x108fd6 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x178)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x108fde [0x48, 0x31, 0x44, 0x24, 0x28] (StorePre 0x108fde 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x108fde + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108fde 5 64 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x108fde 5 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (xor_m64_r64_effect_step 0x108fde 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x108fe3 [0x48, 0x8B, 0x84, 0x24, 0x80, 0x01, 0x00, 0x00] (LoadPre 0x108fe3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x108fe3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108fe3 0 (.sib 4 none 0 (.d32 0x180)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108fe3 0 (.sib 4 none 0 (.d32 0x180))).toInstrSpec (mov_r64_m64_effect_step 0x108fe3 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x180)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x108feb [0x48, 0x31, 0x44, 0x24, 0x30] (StorePre 0x108feb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108feb + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108feb 5 64 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x108feb 5 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (xor_m64_r64_effect_step 0x108feb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x108ff0 [0x48, 0x8B, 0x84, 0x24, 0x88, 0x01, 0x00, 0x00] (LoadPre 0x108ff0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x108ff0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108ff0 0 (.sib 4 none 0 (.d32 0x188)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108ff0 0 (.sib 4 none 0 (.d32 0x188))).toInstrSpec (mov_r64_m64_effect_step 0x108ff0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x188)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x108ff8 [0x48, 0x31, 0x44, 0x24, 0x38] (StorePre 0x108ff8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x108ff8 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108ff8 5 64 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x108ff8 5 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (xor_m64_r64_effect_step 0x108ff8 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x108ffd [0x4C, 0x8B, 0x7C, 0x24, 0x40] (LoadPre 0x108ffd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x108ffd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108ffd 15 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x108ffd 15 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x108ffd 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x109002 [0xBD, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109002) (movR32Imm32Effect 0x109002 5 5 0x8)
      [] [] [.reg 5, .rip] :=
    (movR32Imm32Effect_footprint 0x109002 5 5 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x109002 0xbd (by decide) 0x8) pre_rip
  have f16 : InstrSpec 0x109007 [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109007) (fun _ => nopEffect 0x109007 9)
      [] [] [.rip] :=
    (nopEffect_footprint 0x109007 9).toInstrSpec (nop_m_effect_step 0x109007 [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (4, 4), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108faa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (4, 4), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108faf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (4, 4), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fb7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (4, 4), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fbc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (4, 4), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fc4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (4, 4), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fc9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (4, 4), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fd1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (4, 4), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fd6) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (4, 4), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fde) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (4, 4), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fe3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (4, 4), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108feb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (4, 4), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ff0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (4, 4), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ff8) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (4, 4), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ffd) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 71), (4, 4), (12, 12), (13, 13), (14, 14), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109002) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 71), (4, 4), (5, 76), (12, 12), (13, 13), (14, 14), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109007) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 71), (4, 4), (5, 76), (12, 12), (13, 13), (14, 14), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109010) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 79) (by decide) rfl

theorem block_l108fa2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108fa2 :=
  Rest.liftedBlock (rest_l108fa2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108fa2 x hx)

theorem rest_l109010 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109010 bytes_l109010) (entryMap (live .l109010))
      6 0x109010 bytes_l109010 b_l109010 := by
  have f0 : InstrSpec 0x109010 [0x4C, 0x33, 0xBC, 0xEC, 0x50, 0x01, 0x00, 0x00] (LoadPre 0x109010 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x150)) s (0x109010 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109010 15 (.sib 4 (some 5) 3 (.d32 0x150)))
      [.gpr 15, .gpr 4, .gpr 5] [] [.reg 15, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x109010 15 (.sib 4 (some 5) 3 (.d32 0x150))).toInstrSpec (xor_r64_m64_effect_step 0x109010 0x4c (by decide) 7 (.sib 4 (some 5) 3 (.d32 0x150)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x109018 [0x4C, 0x89, 0x7C, 0x24, 0x40] (StorePre 0x109018 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x109018 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109018 15 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109018 15 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x109018 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10901d [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10901d) (movR32Imm32Effect 0x10901d 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10901d 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x10901d 0xbe (by decide) 0x8) pre_rip
  have f3 : InstrSpec 0x109022 [0x48, 0x8D, 0x5C, 0x24, 0x08] (fun s => s.RIP = 0x109022) (leaR64Effect 0x109022 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x109022 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x109022 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x109027 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x109027) (movR64R64Effect 0x109027 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x109027 7 3).toInstrSpec (mov_r64_r64_effect_step 0x109027 0x48 0xdf (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10902a [0xE8, 0x61, 0x7E, 0xFF, 0xFF] (PushPre 0x10902a 5) (callEffect (fun _ => 0x100e90) 0x10902f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10902a 0x100e90 0x10902f).toInstrSpec (call_rel32_effect_step 0x10902a 0xffff7e61 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109018) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10901d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(4, 4), (5, 5), (6, 56), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109022) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(3, 58), (4, 4), (5, 5), (6, 56), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109027) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 58), (4, 4), (5, 5), (6, 56), (7, 60), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10902a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 58), (4, 62), (5, 5), (6, 56), (7, 60), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e90) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 64) (by decide) (by decide) rfl rfl

theorem block_l109010 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109010 :=
  Rest.liftedBlock (rest_l109010 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109010 x hx)

theorem rest_l10902f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10902f bytes_l10902f) (entryMap (live .l10902f))
      2 0x10902f bytes_l10902f b_l10902f := by
  have f0 : InstrSpec 0x10902f [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x10902f) (movR64R64Effect 0x10902f 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10902f 7 3).toInstrSpec (mov_r64_r64_effect_step 0x10902f 0x48 0xdf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x109032 [0xE8, 0x69, 0x72, 0xFF, 0xFF] (PushPre 0x109032 5) (callEffect (fun _ => 0x1002a0) 0x109037)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109032 0x1002a0 0x109037).toInstrSpec (call_rel32_effect_step 0x109032 0xffff7269 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109032) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002a0) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l10902f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10902f :=
  Rest.liftedBlock (rest_l10902f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10902f x hx)

theorem rest_l109037_1 [Bindings] (code : CodeMap) :
    Rest (n := 87) code lifted (codeRange 0x109037 bytes_l109037) [(1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x1090b0 bytes_l109037_1 b_l109037_1 := by
  have f20 : InstrSpec 0x1090b0 [0x48, 0x89, 0x4C, 0x24, 0x38] (StorePre 0x1090b0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1090b0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1090b0 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1090b0 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x1090b0 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x1090b5 [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x1090b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1090b5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090b5 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1090b5 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1090b5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x1090ba [0x48, 0x33, 0x84, 0xEC, 0x90, 0x01, 0x00, 0x00] (LoadPre 0x1090ba (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x190)) s (0x1090ba + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x1090ba 0 (.sib 4 (some 5) 3 (.d32 0x190)))
      [.gpr 0, .gpr 4, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x1090ba 0 (.sib 4 (some 5) 3 (.d32 0x190))).toInstrSpec (xor_r64_m64_effect_step 0x1090ba 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x190)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x1090c2 [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x1090c2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1090c2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1090c2 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1090c2 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x1090c2 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x1090c7 [0x48, 0x83, 0xFD, 0x68] (fun s => s.RIP = 0x1090c7) (cmpR64Imm8Effect 0x1090c7 5 0x68)
      [.gpr 5] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1090c7 5 0x68).toInstrSpec (cmp_r64_imm8_effect_step 0x1090c7 0x48 0xfd 0x68 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090b5) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 88), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090ba) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090c2) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090c7) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f24 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (19, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090cb) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 95) (jcc_rel32_effect_step 0x1090cb 4 0xfffff52f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l109037 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109037 bytes_l109037) (entryMap (live .l109037))
      26 0x109037 bytes_l109037 b_l109037 := by
  have f0 : InstrSpec 0x109037 [0x4C, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x109037 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109037 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109037 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x109037 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109037 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10903c [0x4C, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x10903c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10903c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10903c 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x10903c 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10903c 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x109041 [0x4C, 0x33, 0x94, 0xEC, 0x58, 0x01, 0x00, 0x00] (LoadPre 0x109041 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x158)) s (0x109041 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109041 10 (.sib 4 (some 5) 3 (.d32 0x158)))
      [.gpr 10, .gpr 4, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x109041 10 (.sib 4 (some 5) 3 (.d32 0x158))).toInstrSpec (xor_r64_m64_effect_step 0x109041 0x4c (by decide) 2 (.sib 4 (some 5) 3 (.d32 0x158)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x109049 [0x4C, 0x89, 0x54, 0x24, 0x08] (StorePre 0x109049 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109049 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109049 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109049 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109049 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10904e [0x4C, 0x33, 0x8C, 0xEC, 0x60, 0x01, 0x00, 0x00] (LoadPre 0x10904e (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x160)) s (0x10904e + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x10904e 9 (.sib 4 (some 5) 3 (.d32 0x160)))
      [.gpr 9, .gpr 4, .gpr 5] [] [.reg 9, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x10904e 9 (.sib 4 (some 5) 3 (.d32 0x160))).toInstrSpec (xor_r64_m64_effect_step 0x10904e 0x4c (by decide) 1 (.sib 4 (some 5) 3 (.d32 0x160)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x109056 [0x4C, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x109056 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109056 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109056 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109056 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x109056 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10905b [0x4C, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x10905b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10905b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10905b 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10905b 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10905b 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x109060 [0x4C, 0x33, 0x84, 0xEC, 0x68, 0x01, 0x00, 0x00] (LoadPre 0x109060 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x168)) s (0x109060 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109060 8 (.sib 4 (some 5) 3 (.d32 0x168)))
      [.gpr 8, .gpr 4, .gpr 5] [] [.reg 8, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x109060 8 (.sib 4 (some 5) 3 (.d32 0x168))).toInstrSpec (xor_r64_m64_effect_step 0x109060 0x4c (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x168)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x109068 [0x4C, 0x89, 0x44, 0x24, 0x18] (StorePre 0x109068 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109068 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109068 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109068 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x109068 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10906d [0x48, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x10906d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10906d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10906d 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10906d 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10906d 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x109072 [0x48, 0x33, 0xBC, 0xEC, 0x70, 0x01, 0x00, 0x00] (LoadPre 0x109072 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x170)) s (0x109072 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109072 7 (.sib 4 (some 5) 3 (.d32 0x170)))
      [.gpr 7, .gpr 4, .gpr 5] [] [.reg 7, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x109072 7 (.sib 4 (some 5) 3 (.d32 0x170))).toInstrSpec (xor_r64_m64_effect_step 0x109072 0x48 (by decide) 7 (.sib 4 (some 5) 3 (.d32 0x170)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10907a [0x48, 0x89, 0x7C, 0x24, 0x20] (StorePre 0x10907a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10907a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10907a 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10907a 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10907a 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10907f [0x48, 0x8B, 0x74, 0x24, 0x28] (LoadPre 0x10907f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10907f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10907f 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10907f 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10907f 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x109084 [0x48, 0x33, 0xB4, 0xEC, 0x78, 0x01, 0x00, 0x00] (LoadPre 0x109084 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x178)) s (0x109084 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109084 6 (.sib 4 (some 5) 3 (.d32 0x178)))
      [.gpr 6, .gpr 4, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x109084 6 (.sib 4 (some 5) 3 (.d32 0x178))).toInstrSpec (xor_r64_m64_effect_step 0x109084 0x48 (by decide) 6 (.sib 4 (some 5) 3 (.d32 0x178)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10908c [0x48, 0x89, 0x74, 0x24, 0x28] (StorePre 0x10908c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10908c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10908c 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10908c 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10908c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x109091 [0x48, 0x8B, 0x54, 0x24, 0x30] (LoadPre 0x109091 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109091 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109091 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x109091 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x109091 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x109096 [0x48, 0x33, 0x94, 0xEC, 0x80, 0x01, 0x00, 0x00] (LoadPre 0x109096 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x180)) s (0x109096 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109096 2 (.sib 4 (some 5) 3 (.d32 0x180)))
      [.gpr 2, .gpr 4, .gpr 5] [] [.reg 2, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x109096 2 (.sib 4 (some 5) 3 (.d32 0x180))).toInstrSpec (xor_r64_m64_effect_step 0x109096 0x48 (by decide) 2 (.sib 4 (some 5) 3 (.d32 0x180)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10909e [0x48, 0x89, 0x54, 0x24, 0x30] (StorePre 0x10909e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10909e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10909e 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10909e 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10909e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1090a3 [0x48, 0x8B, 0x4C, 0x24, 0x38] (LoadPre 0x1090a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1090a3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090a3 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1090a3 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1090a3 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x1090a8 [0x48, 0x33, 0x8C, 0xEC, 0x88, 0x01, 0x00, 0x00] (LoadPre 0x1090a8 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x188)) s (0x1090a8 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x1090a8 1 (.sib 4 (some 5) 3 (.d32 0x188)))
      [.gpr 1, .gpr 4, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x1090a8 1 (.sib 4 (some 5) 3 (.d32 0x188))).toInstrSpec (xor_r64_m64_effect_step 0x1090a8 0x48 (by decide) 1 (.sib 4 (some 5) 3 (.d32 0x188)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10903c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 55), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109041) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 55), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109049) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 55), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10904e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109056) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10905b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 63), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109060) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109068) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10906d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 68), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109072) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10907a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10907f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 73), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109084) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10908c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109091) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(2, 78), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109096) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10909e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090a3) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(1, 83), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090a8) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090b0) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109037_1 code

theorem block_l109037 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109037 :=
  Rest.liftedBlock (rest_l109037 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109037 x hx)

theorem rest_l1090d1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1090d1 bytes_l1090d1) (entryMap (live .l1090d1))
      3 0x1090d1 bytes_l1090d1 b_l1090d1 := by
  have f0 : InstrSpec 0x1090d1 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1090d1) (movR32Imm32Effect 0x1090d1 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1090d1 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x1090d1 0xbe (by decide) 0x8) pre_rip
  have f1 : InstrSpec 0x1090d6 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x1090d6) (leaR64Effect 0x1090d6 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1090d6 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x1090d6 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1090db [0xE8, 0xB0, 0x7D, 0xFF, 0xFF] (PushPre 0x1090db 5) (callEffect (fun _ => 0x100e90) 0x1090e0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1090db 0x100e90 0x1090e0).toInstrSpec (call_rel32_effect_step 0x1090db 0xffff7db0 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090d6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090db) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 53), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e90) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l1090d1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1090d1 :=
  Rest.liftedBlock (rest_l1090d1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1090d1 x hx)

theorem rest_l1090e0_6 [Bindings] (code : CodeMap) :
    Rest (n := 283) code lifted (codeRange 0x1090e0 bytes_l1090e0) [(0, 276), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]
      17 0x1092d8 bytes_l1090e0_6 b_l1090e0_6 := by
  have f120 : InstrSpec 0x1092d8 [0x48, 0x8B, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x1092d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1092d8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1092d8 2 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1092d8 2 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x1092d8 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f121 : InstrSpec 0x1092e0 [0x4C, 0x31, 0xEA] (fun s => s.RIP = 0x1092e0) (xorR64R64Effect 0x1092e0 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1092e0 2 13).toInstrSpec (xor_r64_r64_effect_step 0x1092e0 0x4c 0xea (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x1092e3 [0x4C, 0x31, 0xEE] (fun s => s.RIP = 0x1092e3) (xorR64R64Effect 0x1092e3 6 13)
      [.gpr 6, .gpr 13] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1092e3 6 13).toInstrSpec (xor_r64_r64_effect_step 0x1092e3 0x4c 0xee (by decide) (by decide)) pre_rip
  have f123 : InstrSpec 0x1092e6 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x1092e6) (movR64R64Effect 0x1092e6 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1092e6 0 2).toInstrSpec (mov_r64_r64_effect_step 0x1092e6 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f124 : InstrSpec 0x1092e9 [0x48, 0xC1, 0xC0, 0x20] (fun s => s.RIP = 0x1092e9) (rolR64Effect 0x1092e9 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x1092e9 4 0 32).toInstrSpec (rol_r64_imm8_effect_step 0x1092e9 0x48 0xc0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f125 : InstrSpec 0x1092ed [0x48, 0x33, 0x84, 0xEC, 0xC8, 0x01, 0x00, 0x00] (LoadPre 0x1092ed (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1c8)) s (0x1092ed + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x1092ed 0 (.sib 4 (some 5) 3 (.d32 0x1c8)))
      [.gpr 0, .gpr 4, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x1092ed 0 (.sib 4 (some 5) 3 (.d32 0x1c8))).toInstrSpec (xor_r64_m64_effect_step 0x1092ed 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x1c8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f126 : InstrSpec 0x1092f5 [0x48, 0x31, 0xC6] (fun s => s.RIP = 0x1092f5) (xorR64R64Effect 0x1092f5 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1092f5 6 0).toInstrSpec (xor_r64_r64_effect_step 0x1092f5 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f127 : InstrSpec 0x1092f8 [0x48, 0x89, 0x74, 0x24, 0x38] (StorePre 0x1092f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1092f8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1092f8 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1092f8 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x1092f8 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f128 : InstrSpec 0x1092fd [0x48, 0x31, 0xCA] (fun s => s.RIP = 0x1092fd) (xorR64R64Effect 0x1092fd 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1092fd 2 1).toInstrSpec (xor_r64_r64_effect_step 0x1092fd 0x48 0xca (by decide) (by decide)) pre_rip
  have f129 : InstrSpec 0x109300 [0x49, 0xC1, 0xC6, 0x20] (fun s => s.RIP = 0x109300) (rolR64Effect 0x109300 4 14 32)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (rolR64Effect_footprint 0x109300 4 14 32).toInstrSpec (rol_r64_imm8_effect_step 0x109300 0x49 0xc6 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f130 : InstrSpec 0x109304 [0x4C, 0x33, 0xB4, 0xEC, 0xD0, 0x01, 0x00, 0x00] (LoadPre 0x109304 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1d0)) s (0x109304 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109304 14 (.sib 4 (some 5) 3 (.d32 0x1d0)))
      [.gpr 14, .gpr 4, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x109304 14 (.sib 4 (some 5) 3 (.d32 0x1d0))).toInstrSpec (xor_r64_m64_effect_step 0x109304 0x4c (by decide) 6 (.sib 4 (some 5) 3 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f131 : InstrSpec 0x10930c [0x4C, 0x31, 0xF2] (fun s => s.RIP = 0x10930c) (xorR64R64Effect 0x10930c 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10930c 2 14).toInstrSpec (xor_r64_r64_effect_step 0x10930c 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f132 : InstrSpec 0x10930f [0x48, 0x89, 0x54, 0x24, 0x40] (StorePre 0x10930f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10930f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10930f 2 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10930f 2 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x10930f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f133 : InstrSpec 0x109314 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109314) (movR32Imm32Effect 0x109314 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x109314 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x109314 0xbe (by decide) 0x8) pre_rip
  have f134 : InstrSpec 0x109319 [0x48, 0x8D, 0x5C, 0x24, 0x08] (fun s => s.RIP = 0x109319) (leaR64Effect 0x109319 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x109319 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x109319 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f135 : InstrSpec 0x10931e [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x10931e) (movR64R64Effect 0x10931e 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10931e 7 3).toInstrSpec (mov_r64_r64_effect_step 0x10931e 0x48 0xdf (by decide) (by decide)) pre_rip
  have f136 : InstrSpec 0x109321 [0xE8, 0x6A, 0x7B, 0xFF, 0xFF] (PushPre 0x109321 5) (callEffect (fun _ => 0x100e90) 0x109326)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109321 0x100e90 0x109326).toInstrSpec (call_rel32_effect_step 0x109321 0xffff7b6a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 283) (RestInside.out (n := 283) f120 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 284) (ρ' := [(0, 276), (1, 187), (2, 283), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092e0) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 285) (RestInside.out (n := 285) f121 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 286) (ρ' := [(0, 276), (1, 187), (2, 285), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092e3) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 287) (RestInside.out (n := 287) f122 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 288) (ρ' := [(0, 276), (1, 187), (2, 285), (3, 216), (4, 4), (5, 5), (6, 287), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092e6) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 289) (RestInside.out (n := 289) f123 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 290) (ρ' := [(0, 289), (1, 187), (2, 285), (3, 216), (4, 4), (5, 5), (6, 287), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092e9) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 291) (RestInside.out (n := 291) f124 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 292) (ρ' := [(0, 291), (1, 187), (2, 285), (3, 216), (4, 4), (5, 5), (6, 287), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092ed) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 293) (RestInside.out (n := 293) f125 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 294) (ρ' := [(0, 293), (1, 187), (2, 285), (3, 216), (4, 4), (5, 5), (6, 287), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092f5) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 295) (RestInside.out (n := 295) f126 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 296) (ρ' := [(0, 293), (1, 187), (2, 285), (3, 216), (4, 4), (5, 5), (6, 295), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092f8) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 297) (RestInside.exec (n := 297) (ρ' := [(0, 293), (1, 187), (2, 285), (3, 216), (4, 4), (5, 5), (6, 295), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092fd) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 298) (RestInside.out (n := 298) f128 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 299) (ρ' := [(0, 293), (1, 187), (2, 298), (3, 216), (4, 4), (5, 5), (6, 295), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109300) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 300) (RestInside.out (n := 300) f129 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 301) (ρ' := [(0, 293), (1, 187), (2, 298), (3, 216), (4, 4), (5, 5), (6, 295), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 300), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109304) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f130 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 303) (ρ' := [(0, 293), (1, 187), (2, 298), (3, 216), (4, 4), (5, 5), (6, 295), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 302), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10930c) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f131 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 305) (ρ' := [(0, 293), (1, 187), (2, 304), (3, 216), (4, 4), (5, 5), (6, 295), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 302), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10930f) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 306) (RestInside.exec (n := 306) (ρ' := [(0, 293), (1, 187), (2, 304), (3, 216), (4, 4), (5, 5), (6, 295), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 302), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109314) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 307) (RestInside.out (n := 307) f133 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 308) (ρ' := [(0, 293), (1, 187), (2, 304), (3, 216), (4, 4), (5, 5), (6, 307), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 302), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109319) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 309) (RestInside.out (n := 309) f134 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 310) (ρ' := [(0, 293), (1, 187), (2, 304), (3, 309), (4, 4), (5, 5), (6, 307), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 302), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10931e) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 311) (RestInside.out (n := 311) f135 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 312) (ρ' := [(0, 293), (1, 187), (2, 304), (3, 309), (4, 4), (5, 5), (6, 307), (7, 311), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 302), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109321) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 313) (RestInside.out (n := 313) f136 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 314) (ρ' := [(0, 293), (1, 187), (2, 304), (3, 309), (4, 313), (5, 5), (6, 307), (7, 311), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 302), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e90) f136 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 315) (by decide) (by decide) rfl rfl

theorem rest_l1090e0_5 [Bindings] (code : CodeMap) :
    Rest (n := 246) code lifted (codeRange 0x1090e0 bytes_l1090e0) [(0, 238), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 244), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]
      37 0x10927e bytes_l1090e0_5 b_l1090e0_5 := by
  have f100 : InstrSpec 0x10927e [0x4C, 0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x10927e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10927e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10927e 8 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10927e 8 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x10927e 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f101 : InstrSpec 0x109286 [0x49, 0x31, 0xD0] (fun s => s.RIP = 0x109286) (xorR64R64Effect 0x109286 8 2)
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109286 8 2).toInstrSpec (xor_r64_r64_effect_step 0x109286 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x109289 [0x48, 0x89, 0x7C, 0x24, 0x20] (StorePre 0x109289 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109289 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109289 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109289 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x109289 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f103 : InstrSpec 0x10928e [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x10928e) (movR64R64Effect 0x10928e 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10928e 0 8).toInstrSpec (mov_r64_r64_effect_step 0x10928e 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f104 : InstrSpec 0x109291 [0x48, 0xC1, 0xC0, 0x20] (fun s => s.RIP = 0x109291) (rolR64Effect 0x109291 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x109291 4 0 32).toInstrSpec (rol_r64_imm8_effect_step 0x109291 0x48 0xc0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x109295 [0x48, 0x31, 0xD6] (fun s => s.RIP = 0x109295) (xorR64R64Effect 0x109295 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109295 6 2).toInstrSpec (xor_r64_r64_effect_step 0x109295 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f106 : InstrSpec 0x109298 [0x48, 0x33, 0x84, 0xEC, 0xB8, 0x01, 0x00, 0x00] (LoadPre 0x109298 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1b8)) s (0x109298 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109298 0 (.sib 4 (some 5) 3 (.d32 0x1b8)))
      [.gpr 0, .gpr 4, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x109298 0 (.sib 4 (some 5) 3 (.d32 0x1b8))).toInstrSpec (xor_r64_m64_effect_step 0x109298 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x1b8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f107 : InstrSpec 0x1092a0 [0x4C, 0x31, 0xF6] (fun s => s.RIP = 0x1092a0) (xorR64R64Effect 0x1092a0 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1092a0 6 14).toInstrSpec (xor_r64_r64_effect_step 0x1092a0 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x1092a3 [0x48, 0x31, 0xC6] (fun s => s.RIP = 0x1092a3) (xorR64R64Effect 0x1092a3 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1092a3 6 0).toInstrSpec (xor_r64_r64_effect_step 0x1092a3 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f109 : InstrSpec 0x1092a6 [0x48, 0x8B, 0x54, 0x24, 0x78] (LoadPre 0x1092a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1092a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1092a6 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1092a6 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x1092a6 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f110 : InstrSpec 0x1092ab [0x48, 0x8B, 0xBC, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x1092ab (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1092ab + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1092ab 7 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1092ab 7 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x1092ab 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f111 : InstrSpec 0x1092b3 [0x48, 0x31, 0xFA] (fun s => s.RIP = 0x1092b3) (xorR64R64Effect 0x1092b3 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1092b3 2 7).toInstrSpec (xor_r64_r64_effect_step 0x1092b3 0x48 0xfa (by decide) (by decide)) pre_rip
  have f112 : InstrSpec 0x1092b6 [0x48, 0x89, 0x74, 0x24, 0x28] (StorePre 0x1092b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1092b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1092b6 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1092b6 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1092b6 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f113 : InstrSpec 0x1092bb [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x1092bb) (movR64R64Effect 0x1092bb 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1092bb 0 2).toInstrSpec (mov_r64_r64_effect_step 0x1092bb 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f114 : InstrSpec 0x1092be [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x1092be) (movR64R64Effect 0x1092be 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1092be 6 2).toInstrSpec (mov_r64_r64_effect_step 0x1092be 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x1092c1 [0x48, 0xC1, 0xC0, 0x20] (fun s => s.RIP = 0x1092c1) (rolR64Effect 0x1092c1 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x1092c1 4 0 32).toInstrSpec (rol_r64_imm8_effect_step 0x1092c1 0x48 0xc0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f116 : InstrSpec 0x1092c5 [0x48, 0x33, 0x84, 0xEC, 0xC0, 0x01, 0x00, 0x00] (LoadPre 0x1092c5 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1c0)) s (0x1092c5 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x1092c5 0 (.sib 4 (some 5) 3 (.d32 0x1c0)))
      [.gpr 0, .gpr 4, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x1092c5 0 (.sib 4 (some 5) 3 (.d32 0x1c0))).toInstrSpec (xor_r64_m64_effect_step 0x1092c5 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x1c0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f117 : InstrSpec 0x1092cd [0x49, 0x31, 0xF8] (fun s => s.RIP = 0x1092cd) (xorR64R64Effect 0x1092cd 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1092cd 8 7).toInstrSpec (xor_r64_r64_effect_step 0x1092cd 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x1092d0 [0x49, 0x31, 0xC0] (fun s => s.RIP = 0x1092d0) (xorR64R64Effect 0x1092d0 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1092d0 8 0).toInstrSpec (xor_r64_r64_effect_step 0x1092d0 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f119 : InstrSpec 0x1092d3 [0x4C, 0x89, 0x44, 0x24, 0x30] (StorePre 0x1092d3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1092d3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1092d3 8 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1092d3 8 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1092d3 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 246) (RestInside.out (n := 246) f100 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 247) (ρ' := [(0, 238), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 244), (8, 246), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109286) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 248) (RestInside.out (n := 248) f101 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 249) (ρ' := [(0, 238), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109289) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 250) (RestInside.exec (n := 250) (ρ' := [(0, 238), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10928e) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 251) (RestInside.out (n := 251) f103 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 252) (ρ' := [(0, 251), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109291) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 253) (RestInside.out (n := 253) f104 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 254) (ρ' := [(0, 253), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109295) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 255) (RestInside.out (n := 255) f105 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 256) (ρ' := [(0, 253), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 255), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109298) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 257) (RestInside.out (n := 257) f106 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 258) (ρ' := [(0, 257), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 255), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092a0) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f107 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 260) (ρ' := [(0, 257), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 259), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092a3) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 261) (RestInside.out (n := 261) f108 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 262) (ρ' := [(0, 257), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 261), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092a6) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 263) (RestInside.out (n := 263) f109 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 264) (ρ' := [(0, 257), (1, 187), (2, 263), (3, 216), (4, 4), (5, 5), (6, 261), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092ab) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 265) (RestInside.out (n := 265) f110 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 266) (ρ' := [(0, 257), (1, 187), (2, 263), (3, 216), (4, 4), (5, 5), (6, 261), (7, 265), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092b3) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 267) (RestInside.out (n := 267) f111 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 268) (ρ' := [(0, 257), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 261), (7, 265), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092b6) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 269) (RestInside.exec (n := 269) (ρ' := [(0, 257), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 261), (7, 265), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092bb) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 270) (RestInside.out (n := 270) f113 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 271) (ρ' := [(0, 270), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 261), (7, 265), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092be) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 272) (RestInside.out (n := 272) f114 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 273) (ρ' := [(0, 270), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092c1) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 274) (RestInside.out (n := 274) f115 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 275) (ρ' := [(0, 274), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092c5) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 276) (RestInside.out (n := 276) f116 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 277) (ρ' := [(0, 276), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092cd) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 278) (RestInside.out (n := 278) f117 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 279) (ρ' := [(0, 276), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 278), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092d0) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 280) (RestInside.out (n := 280) f118 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 281) (ρ' := [(0, 276), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092d3) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 282) (RestInside.exec (n := 282) (ρ' := [(0, 276), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092d8) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1090e0_6 code

theorem rest_l1090e0_4 [Bindings] (code : CodeMap) :
    Rest (n := 208) code lifted (codeRange 0x1090e0 bytes_l1090e0) [(0, 111), (1, 187), (2, 138), (3, 206), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]
      57 0x10922c bytes_l1090e0_4 b_l1090e0_4 := by
  have f80 : InstrSpec 0x10922c [0x4D, 0x89, 0xD8] (fun s => s.RIP = 0x10922c) (movR64R64Effect 0x10922c 8 11)
      [.gpr 11] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10922c 8 11).toInstrSpec (mov_r64_r64_effect_step 0x10922c 0x4d 0xd8 (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x10922f [0x49, 0xC1, 0xC0, 0x20] (fun s => s.RIP = 0x10922f) (rolR64Effect 0x10922f 4 8 32)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (rolR64Effect_footprint 0x10922f 4 8 32).toInstrSpec (rol_r64_imm8_effect_step 0x10922f 0x49 0xc0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x109233 [0x4C, 0x33, 0x84, 0xEC, 0xA0, 0x01, 0x00, 0x00] (LoadPre 0x109233 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1a0)) s (0x109233 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109233 8 (.sib 4 (some 5) 3 (.d32 0x1a0)))
      [.gpr 8, .gpr 4, .gpr 5] [] [.reg 8, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x109233 8 (.sib 4 (some 5) 3 (.d32 0x1a0))).toInstrSpec (xor_r64_m64_effect_step 0x109233 0x4c (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x1a0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f83 : InstrSpec 0x10923b [0x4C, 0x31, 0xF3] (fun s => s.RIP = 0x10923b) (xorR64R64Effect 0x10923b 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10923b 3 14).toInstrSpec (xor_r64_r64_effect_step 0x10923b 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x10923e [0x4C, 0x31, 0xC3] (fun s => s.RIP = 0x10923e) (xorR64R64Effect 0x10923e 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10923e 3 8).toInstrSpec (xor_r64_r64_effect_step 0x10923e 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x109241 [0x48, 0x89, 0x5C, 0x24, 0x10] (StorePre 0x109241 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109241 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109241 3 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109241 3 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x109241 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f86 : InstrSpec 0x109246 [0x48, 0x31, 0xC7] (fun s => s.RIP = 0x109246) (xorR64R64Effect 0x109246 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109246 7 0).toInstrSpec (xor_r64_r64_effect_step 0x109246 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x109249 [0x49, 0x31, 0xC3] (fun s => s.RIP = 0x109249) (xorR64R64Effect 0x109249 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109249 11 0).toInstrSpec (xor_r64_r64_effect_step 0x109249 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x10924c [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x10924c) (movR64R64Effect 0x10924c 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10924c 0 7).toInstrSpec (mov_r64_r64_effect_step 0x10924c 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x10924f [0x48, 0xC1, 0xC0, 0x20] (fun s => s.RIP = 0x10924f) (rolR64Effect 0x10924f 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x10924f 4 0 32).toInstrSpec (rol_r64_imm8_effect_step 0x10924f 0x48 0xc0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f90 : InstrSpec 0x109253 [0x48, 0x33, 0x84, 0xEC, 0xA8, 0x01, 0x00, 0x00] (LoadPre 0x109253 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1a8)) s (0x109253 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109253 0 (.sib 4 (some 5) 3 (.d32 0x1a8)))
      [.gpr 0, .gpr 4, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x109253 0 (.sib 4 (some 5) 3 (.d32 0x1a8))).toInstrSpec (xor_r64_m64_effect_step 0x109253 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x1a8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f91 : InstrSpec 0x10925b [0x49, 0x31, 0xC3] (fun s => s.RIP = 0x10925b) (xorR64R64Effect 0x10925b 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10925b 11 0).toInstrSpec (xor_r64_r64_effect_step 0x10925b 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x10925e [0x4C, 0x31, 0xFE] (fun s => s.RIP = 0x10925e) (xorR64R64Effect 0x10925e 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10925e 6 15).toInstrSpec (xor_r64_r64_effect_step 0x10925e 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f93 : InstrSpec 0x109261 [0x4C, 0x89, 0x5C, 0x24, 0x18] (StorePre 0x109261 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109261 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109261 11 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109261 11 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x109261 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f94 : InstrSpec 0x109266 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x109266) (movR64R64Effect 0x109266 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109266 0 6).toInstrSpec (mov_r64_r64_effect_step 0x109266 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x109269 [0x48, 0xC1, 0xC0, 0x20] (fun s => s.RIP = 0x109269) (rolR64Effect 0x109269 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x109269 4 0 32).toInstrSpec (rol_r64_imm8_effect_step 0x109269 0x48 0xc0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f96 : InstrSpec 0x10926d [0x48, 0x33, 0x84, 0xEC, 0xB0, 0x01, 0x00, 0x00] (LoadPre 0x10926d (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1b0)) s (0x10926d + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x10926d 0 (.sib 4 (some 5) 3 (.d32 0x1b0)))
      [.gpr 0, .gpr 4, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x10926d 0 (.sib 4 (some 5) 3 (.d32 0x1b0))).toInstrSpec (xor_r64_m64_effect_step 0x10926d 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x1b0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f97 : InstrSpec 0x109275 [0x4C, 0x31, 0xFF] (fun s => s.RIP = 0x109275) (xorR64R64Effect 0x109275 7 15)
      [.gpr 7, .gpr 15] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109275 7 15).toInstrSpec (xor_r64_r64_effect_step 0x109275 0x4c 0xff (by decide) (by decide)) pre_rip
  have f98 : InstrSpec 0x109278 [0x4C, 0x31, 0xF7] (fun s => s.RIP = 0x109278) (xorR64R64Effect 0x109278 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109278 7 14).toInstrSpec (xor_r64_r64_effect_step 0x109278 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x10927b [0x48, 0x31, 0xC7] (fun s => s.RIP = 0x10927b) (xorR64R64Effect 0x10927b 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10927b 7 0).toInstrSpec (xor_r64_r64_effect_step 0x10927b 0x48 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f80 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 206), (4, 4), (5, 5), (6, 59), (7, 57), (8, 208), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10922f) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f81 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 206), (4, 4), (5, 5), (6, 59), (7, 57), (8, 210), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109233) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f82 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 206), (4, 4), (5, 5), (6, 59), (7, 57), (8, 212), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10923b) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f83 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 214), (4, 4), (5, 5), (6, 59), (7, 57), (8, 212), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10923e) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f84 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 59), (7, 57), (8, 212), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109241) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 218) (RestInside.exec (n := 218) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 59), (7, 57), (8, 212), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109246) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f86 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 59), (7, 219), (8, 212), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109249) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f87 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 59), (7, 219), (8, 212), (9, 201), (10, 197), (11, 221), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10924c) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f88 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(0, 223), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 59), (7, 219), (8, 212), (9, 201), (10, 197), (11, 221), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10924f) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f89 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(0, 225), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 59), (7, 219), (8, 212), (9, 201), (10, 197), (11, 221), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109253) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f90 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 227), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 59), (7, 219), (8, 212), (9, 201), (10, 197), (11, 221), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10925b) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.out (n := 229) f91 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 230) (ρ' := [(0, 227), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 59), (7, 219), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10925e) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.out (n := 231) f92 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 232) (ρ' := [(0, 227), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 219), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109261) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 233) (RestInside.exec (n := 233) (ρ' := [(0, 227), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 219), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109266) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f94 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 234), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 219), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109269) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f95 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 237) (ρ' := [(0, 236), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 219), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10926d) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f96 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 239) (ρ' := [(0, 238), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 219), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109275) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f97 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 241) (ρ' := [(0, 238), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 240), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109278) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 242) (RestInside.out (n := 242) f98 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 243) (ρ' := [(0, 238), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 242), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10927b) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 244) (RestInside.out (n := 244) f99 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 245) (ρ' := [(0, 238), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 244), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10927e) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1090e0_5 code

theorem rest_l1090e0_3 [Bindings] (code : CodeMap) :
    Rest (n := 169) code lifted (codeRange 0x1090e0 bytes_l1090e0) [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 161), (11, 55), (12, 156), (13, 167), (14, 163), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]
      77 0x1091d6 bytes_l1090e0_3 b_l1090e0_3 := by
  have f60 : InstrSpec 0x1091d6 [0x4C, 0x8B, 0x74, 0x24, 0x40] (LoadPre 0x1091d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1091d6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1091d6 14 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x1091d6 14 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1091d6 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f61 : InstrSpec 0x1091db [0x4D, 0x89, 0xF2] (fun s => s.RIP = 0x1091db) (movR64R64Effect 0x1091db 10 14)
      [.gpr 14] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1091db 10 14).toInstrSpec (mov_r64_r64_effect_step 0x1091db 0x4d 0xf2 (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x1091de [0x49, 0xC1, 0xC2, 0x28] (fun s => s.RIP = 0x1091de) (rolR64Effect 0x1091de 4 10 40)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR64Effect_footprint 0x1091de 4 10 40).toInstrSpec (rol_r64_imm8_effect_step 0x1091de 0x49 0xc2 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x1091e2 [0x48, 0xB9, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00] (fun s => s.RIP = 0x1091e2) (movR64Imm64Effect 0x1091e2 1 0xff00ff00ff00ff)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x1091e2 1 0xff00ff00ff00ff).toInstrSpec (mov_r64_imm64_effect_step 0x1091e2 0x48 0xb9 (by decide) (by decide) 0xff00ff00ff00ff) pre_rip
  have f64 : InstrSpec 0x1091ec [0x49, 0x21, 0xCA] (fun s => s.RIP = 0x1091ec) (andR64R64Effect 0x1091ec 10 1)
      [.gpr 10, .gpr 1] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1091ec 10 1).toInstrSpec (and_r64_r64_effect_step 0x1091ec 0x49 0xca (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x1091ef [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x1091ef) (movR64R64Effect 0x1091ef 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1091ef 1 14).toInstrSpec (mov_r64_r64_effect_step 0x1091ef 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x1091f2 [0x48, 0xC1, 0xC1, 0x38] (fun s => s.RIP = 0x1091f2) (rolR64Effect 0x1091f2 4 1 56)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR64Effect_footprint 0x1091f2 4 1 56).toInstrSpec (rol_r64_imm8_effect_step 0x1091f2 0x48 0xc1 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x1091f6 [0x49, 0xBC, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF] (fun s => s.RIP = 0x1091f6) (movR64Imm64Effect 0x1091f6 12 0xff00ff00ff00ff00)
      [] [] [.reg 12, .rip] :=
    (movR64Imm64Effect_footprint 0x1091f6 12 0xff00ff00ff00ff00).toInstrSpec (mov_r64_imm64_effect_step 0x1091f6 0x49 0xbc (by decide) (by decide) 0xff00ff00ff00ff00) pre_rip
  have f68 : InstrSpec 0x109200 [0x4C, 0x21, 0xE1] (fun s => s.RIP = 0x109200) (andR64R64Effect 0x109200 1 12)
      [.gpr 1, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109200 1 12).toInstrSpec (and_r64_r64_effect_step 0x109200 0x4c 0xe1 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x109203 [0x4C, 0x09, 0xD1] (fun s => s.RIP = 0x109203) (orR64R64Effect 0x109203 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109203 1 10).toInstrSpec (or_r64_r64_effect_step 0x109203 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x109206 [0x4C, 0x31, 0xCB] (fun s => s.RIP = 0x109206) (xorR64R64Effect 0x109206 3 9)
      [.gpr 3, .gpr 9] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109206 3 9).toInstrSpec (xor_r64_r64_effect_step 0x109206 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x109209 [0x49, 0x31, 0xCE] (fun s => s.RIP = 0x109209) (xorR64R64Effect 0x109209 14 1)
      [.gpr 14, .gpr 1] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109209 14 1).toInstrSpec (xor_r64_r64_effect_step 0x109209 0x49 0xce (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x10920c [0x49, 0x89, 0xDA] (fun s => s.RIP = 0x10920c) (movR64R64Effect 0x10920c 10 3)
      [.gpr 3] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10920c 10 3).toInstrSpec (mov_r64_r64_effect_step 0x10920c 0x49 0xda (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x10920f [0x49, 0xC1, 0xC2, 0x20] (fun s => s.RIP = 0x10920f) (rolR64Effect 0x10920f 4 10 32)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR64Effect_footprint 0x10920f 4 10 32).toInstrSpec (rol_r64_imm8_effect_step 0x10920f 0x49 0xc2 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x109213 [0x4C, 0x33, 0x94, 0xEC, 0x98, 0x01, 0x00, 0x00] (LoadPre 0x109213 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x198)) s (0x109213 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109213 10 (.sib 4 (some 5) 3 (.d32 0x198)))
      [.gpr 10, .gpr 4, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x109213 10 (.sib 4 (some 5) 3 (.d32 0x198))).toInstrSpec (xor_r64_m64_effect_step 0x109213 0x4c (by decide) 2 (.sib 4 (some 5) 3 (.d32 0x198)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f75 : InstrSpec 0x10921b [0x4D, 0x31, 0xF1] (fun s => s.RIP = 0x10921b) (xorR64R64Effect 0x10921b 9 14)
      [.gpr 9, .gpr 14] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10921b 9 14).toInstrSpec (xor_r64_r64_effect_step 0x10921b 0x4d 0xf1 (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x10921e [0x4D, 0x31, 0xD1] (fun s => s.RIP = 0x10921e) (xorR64R64Effect 0x10921e 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10921e 9 10).toInstrSpec (xor_r64_r64_effect_step 0x10921e 0x4d 0xd1 (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x109221 [0x4C, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x109221 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109221 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109221 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109221 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109221 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f78 : InstrSpec 0x109226 [0x4D, 0x31, 0xC3] (fun s => s.RIP = 0x109226) (xorR64R64Effect 0x109226 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109226 11 8).toInstrSpec (xor_r64_r64_effect_step 0x109226 0x4d 0xc3 (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x109229 [0x4C, 0x31, 0xC3] (fun s => s.RIP = 0x109229) (xorR64R64Effect 0x109229 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109229 3 8).toInstrSpec (xor_r64_r64_effect_step 0x109229 0x4c 0xc3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f60 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 161), (11, 55), (12, 156), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091db) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f61 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 171), (11, 55), (12, 156), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091de) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f62 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 173), (11, 55), (12, 156), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091e2) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f63 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 111), (1, 175), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 173), (11, 55), (12, 156), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091ec) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f64 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 111), (1, 175), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 177), (11, 55), (12, 156), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091ef) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f65 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 111), (1, 179), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 177), (11, 55), (12, 156), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091f2) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f66 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 111), (1, 181), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 177), (11, 55), (12, 156), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091f6) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f67 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 111), (1, 181), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 177), (11, 55), (12, 183), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109200) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f68 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 111), (1, 185), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 177), (11, 55), (12, 183), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109203) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f69 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 177), (11, 55), (12, 183), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109206) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f70 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 177), (11, 55), (12, 183), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109209) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f71 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 177), (11, 55), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10920c) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f72 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 193), (11, 55), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10920f) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f73 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 195), (11, 55), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109213) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f74 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 197), (11, 55), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10921b) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f75 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 199), (10, 197), (11, 55), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10921e) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f76 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 201), (10, 197), (11, 55), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109221) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.exec (n := 203) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 201), (10, 197), (11, 55), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109226) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f78 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109229) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f79 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 206), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10922c) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1090e0_4 code

theorem rest_l1090e0_2 [Bindings] (code : CodeMap) :
    Rest (n := 132) code lifted (codeRange 0x1090e0 bytes_l1090e0) [(0, 111), (1, 79), (2, 127), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 130), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]
      97 0x109182 bytes_l1090e0_2 b_l1090e0_2 := by
  have f40 : InstrSpec 0x109182 [0x4D, 0x21, 0xEA] (fun s => s.RIP = 0x109182) (andR64R64Effect 0x109182 10 13)
      [.gpr 10, .gpr 13] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109182 10 13).toInstrSpec (and_r64_r64_effect_step 0x109182 0x4d 0xea (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x109185 [0x48, 0xC1, 0xC2, 0x38] (fun s => s.RIP = 0x109185) (rolR64Effect 0x109185 4 2 56)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR64Effect_footprint 0x109185 4 2 56).toInstrSpec (rol_r64_imm8_effect_step 0x109185 0x48 0xc2 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x109189 [0x48, 0x21, 0xCA] (fun s => s.RIP = 0x109189) (andR64R64Effect 0x109189 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109189 2 1).toInstrSpec (and_r64_r64_effect_step 0x109189 0x48 0xca (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x10918c [0x4C, 0x09, 0xD2] (fun s => s.RIP = 0x10918c) (orR64R64Effect 0x10918c 2 10)
      [.gpr 2, .gpr 10] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10918c 2 10).toInstrSpec (or_r64_r64_effect_step 0x10918c 0x4c 0xd2 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x10918f [0x4C, 0x89, 0x64, 0x24, 0x78] (StorePre 0x10918f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10918f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10918f 12 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10918f 12 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x10918f 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x109194 [0x4D, 0x89, 0xE2] (fun s => s.RIP = 0x109194) (movR64R64Effect 0x109194 10 12)
      [.gpr 12] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x109194 10 12).toInstrSpec (mov_r64_r64_effect_step 0x109194 0x4d 0xe2 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x109197 [0x49, 0xC1, 0xC2, 0x28] (fun s => s.RIP = 0x109197) (rolR64Effect 0x109197 4 10 40)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR64Effect_footprint 0x109197 4 10 40).toInstrSpec (rol_r64_imm8_effect_step 0x109197 0x49 0xc2 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x10919b [0x4D, 0x21, 0xEA] (fun s => s.RIP = 0x10919b) (andR64R64Effect 0x10919b 10 13)
      [.gpr 10, .gpr 13] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10919b 10 13).toInstrSpec (and_r64_r64_effect_step 0x10919b 0x4d 0xea (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x10919e [0x49, 0xC1, 0xC4, 0x38] (fun s => s.RIP = 0x10919e) (rolR64Effect 0x10919e 4 12 56)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (rolR64Effect_footprint 0x10919e 4 12 56).toInstrSpec (rol_r64_imm8_effect_step 0x10919e 0x49 0xc4 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x1091a2 [0x49, 0x21, 0xCC] (fun s => s.RIP = 0x1091a2) (andR64R64Effect 0x1091a2 12 1)
      [.gpr 12, .gpr 1] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1091a2 12 1).toInstrSpec (and_r64_r64_effect_step 0x1091a2 0x49 0xcc (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x1091a5 [0x4D, 0x89, 0xF5] (fun s => s.RIP = 0x1091a5) (movR64R64Effect 0x1091a5 13 14)
      [.gpr 14] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1091a5 13 14).toInstrSpec (mov_r64_r64_effect_step 0x1091a5 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x1091a8 [0x4C, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x1091a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1091a8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091a8 14 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1091a8 14 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x1091a8 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x1091b0 [0x49, 0xC1, 0xC6, 0x28] (fun s => s.RIP = 0x1091b0) (rolR64Effect 0x1091b0 4 14 40)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (rolR64Effect_footprint 0x1091b0 4 14 40).toInstrSpec (rol_r64_imm8_effect_step 0x1091b0 0x49 0xc6 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x1091b4 [0x4D, 0x09, 0xD4] (fun s => s.RIP = 0x1091b4) (orR64R64Effect 0x1091b4 12 10)
      [.gpr 12, .gpr 10] [] [.reg 12, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1091b4 12 10).toInstrSpec (or_r64_r64_effect_step 0x1091b4 0x4d 0xd4 (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x1091b7 [0x4C, 0x89, 0xA4, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x1091b7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1091b7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091b7 12 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1091b7 12 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x1091b7 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f55 : InstrSpec 0x1091bf [0x49, 0xC1, 0xC5, 0x38] (fun s => s.RIP = 0x1091bf) (rolR64Effect 0x1091bf 4 13 56)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (rolR64Effect_footprint 0x1091bf 4 13 56).toInstrSpec (rol_r64_imm8_effect_step 0x1091bf 0x49 0xc5 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x1091c3 [0x49, 0xBA, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00] (fun s => s.RIP = 0x1091c3) (movR64Imm64Effect 0x1091c3 10 0xff00ff00ff00ff)
      [] [] [.reg 10, .rip] :=
    (movR64Imm64Effect_footprint 0x1091c3 10 0xff00ff00ff00ff).toInstrSpec (mov_r64_imm64_effect_step 0x1091c3 0x49 0xba (by decide) (by decide) 0xff00ff00ff00ff) pre_rip
  have f57 : InstrSpec 0x1091cd [0x4D, 0x21, 0xD6] (fun s => s.RIP = 0x1091cd) (andR64R64Effect 0x1091cd 14 10)
      [.gpr 14, .gpr 10] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1091cd 14 10).toInstrSpec (and_r64_r64_effect_step 0x1091cd 0x4d 0xd6 (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x1091d0 [0x49, 0x21, 0xCD] (fun s => s.RIP = 0x1091d0) (andR64R64Effect 0x1091d0 13 1)
      [.gpr 13, .gpr 1] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1091d0 13 1).toInstrSpec (and_r64_r64_effect_step 0x1091d0 0x49 0xcd (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x1091d3 [0x4D, 0x09, 0xF5] (fun s => s.RIP = 0x1091d3) (orR64R64Effect 0x1091d3 13 14)
      [.gpr 13, .gpr 14] [] [.reg 13, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1091d3 13 14).toInstrSpec (or_r64_r64_effect_step 0x1091d3 0x4d 0xf5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f40 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 111), (1, 79), (2, 127), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 132), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109185) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f41 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 111), (1, 79), (2, 134), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 132), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109189) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f42 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 111), (1, 79), (2, 136), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 132), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10918c) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f43 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 132), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10918f) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.exec (n := 140) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 132), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109194) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f45 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 141), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109197) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f46 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 143), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10919b) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f47 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10919e) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f48 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 147), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091a2) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f49 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 149), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091a5) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f50 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 149), (13, 151), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091a8) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.exec (n := 153) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 149), (13, 151), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091b0) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f52 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 149), (13, 151), (14, 154), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091b4) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f53 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 156), (13, 151), (14, 154), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091b7) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.exec (n := 158) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 156), (13, 151), (14, 154), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091bf) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f55 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 156), (13, 159), (14, 154), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091c3) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f56 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 161), (11, 55), (12, 156), (13, 159), (14, 154), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091cd) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f57 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 161), (11, 55), (12, 156), (13, 159), (14, 163), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091d0) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f58 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 161), (11, 55), (12, 156), (13, 165), (14, 163), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091d3) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f59 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 161), (11, 55), (12, 156), (13, 167), (14, 163), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091d6) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1090e0_3 code

theorem rest_l1090e0_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x1090e0 bytes_l1090e0) [(0, 89), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 91), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]
      117 0x10913b bytes_l1090e0_1 b_l1090e0_1 := by
  have f20 : InstrSpec 0x10913b [0x49, 0xC1, 0xC0, 0x38] (fun s => s.RIP = 0x10913b) (rolR64Effect 0x10913b 4 8 56)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (rolR64Effect_footprint 0x10913b 4 8 56).toInstrSpec (rol_r64_imm8_effect_step 0x10913b 0x49 0xc0 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x10913f [0x49, 0x21, 0xC8] (fun s => s.RIP = 0x10913f) (andR64R64Effect 0x10913f 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10913f 8 1).toInstrSpec (and_r64_r64_effect_step 0x10913f 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x109142 [0x48, 0x89, 0xFA] (fun s => s.RIP = 0x109142) (movR64R64Effect 0x109142 2 7)
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x109142 2 7).toInstrSpec (mov_r64_r64_effect_step 0x109142 0x48 0xfa (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x109145 [0x48, 0xC1, 0xC2, 0x28] (fun s => s.RIP = 0x109145) (rolR64Effect 0x109145 4 2 40)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR64Effect_footprint 0x109145 4 2 40).toInstrSpec (rol_r64_imm8_effect_step 0x109145 0x48 0xc2 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x109149 [0x49, 0x09, 0xC0] (fun s => s.RIP = 0x109149) (orR64R64Effect 0x109149 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109149 8 0).toInstrSpec (or_r64_r64_effect_step 0x109149 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x10914c [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x10914c) (movR64R64Effect 0x10914c 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10914c 0 7).toInstrSpec (mov_r64_r64_effect_step 0x10914c 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10914f [0x48, 0xC1, 0xC0, 0x38] (fun s => s.RIP = 0x10914f) (rolR64Effect 0x10914f 4 0 56)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x10914f 4 0 56).toInstrSpec (rol_r64_imm8_effect_step 0x10914f 0x48 0xc0 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x109153 [0x4C, 0x21, 0xEA] (fun s => s.RIP = 0x109153) (andR64R64Effect 0x109153 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109153 2 13).toInstrSpec (and_r64_r64_effect_step 0x109153 0x4c 0xea (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x109156 [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x109156) (andR64R64Effect 0x109156 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109156 0 1).toInstrSpec (and_r64_r64_effect_step 0x109156 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x109159 [0x48, 0x09, 0xD0] (fun s => s.RIP = 0x109159) (orR64R64Effect 0x109159 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109159 0 2).toInstrSpec (or_r64_r64_effect_step 0x109159 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10915c [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x10915c) (movR64R64Effect 0x10915c 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10915c 2 6).toInstrSpec (mov_r64_r64_effect_step 0x10915c 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x10915f [0x48, 0xC1, 0xC2, 0x28] (fun s => s.RIP = 0x10915f) (rolR64Effect 0x10915f 4 2 40)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR64Effect_footprint 0x10915f 4 2 40).toInstrSpec (rol_r64_imm8_effect_step 0x10915f 0x48 0xc2 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x109163 [0x4C, 0x21, 0xEA] (fun s => s.RIP = 0x109163) (andR64R64Effect 0x109163 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109163 2 13).toInstrSpec (and_r64_r64_effect_step 0x109163 0x4c 0xea (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x109166 [0x49, 0x89, 0xF7] (fun s => s.RIP = 0x109166) (movR64R64Effect 0x109166 15 6)
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x109166 15 6).toInstrSpec (mov_r64_r64_effect_step 0x109166 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x109169 [0x49, 0xC1, 0xC7, 0x38] (fun s => s.RIP = 0x109169) (rolR64Effect 0x109169 4 15 56)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR64Effect_footprint 0x109169 4 15 56).toInstrSpec (rol_r64_imm8_effect_step 0x109169 0x49 0xc7 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x10916d [0x49, 0x21, 0xCF] (fun s => s.RIP = 0x10916d) (andR64R64Effect 0x10916d 15 1)
      [.gpr 15, .gpr 1] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10916d 15 1).toInstrSpec (and_r64_r64_effect_step 0x10916d 0x49 0xcf (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x109170 [0x49, 0x09, 0xD7] (fun s => s.RIP = 0x109170) (orR64R64Effect 0x109170 15 2)
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109170 15 2).toInstrSpec (or_r64_r64_effect_step 0x109170 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x109173 [0x4C, 0x89, 0xD2] (fun s => s.RIP = 0x109173) (movR64R64Effect 0x109173 2 10)
      [.gpr 10] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x109173 2 10).toInstrSpec (mov_r64_r64_effect_step 0x109173 0x4c 0xd2 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x109176 [0x4C, 0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x109176 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x109176 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109176 10 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109176 10 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x109176 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x10917e [0x49, 0xC1, 0xC2, 0x28] (fun s => s.RIP = 0x10917e) (rolR64Effect 0x10917e 4 10 40)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR64Effect_footprint 0x10917e 4 10 40).toInstrSpec (rol_r64_imm8_effect_step 0x10917e 0x49 0xc2 0x28 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 89), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 93), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10913f) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 89), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 95), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109142) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 89), (1, 79), (2, 97), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 95), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109145) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 89), (1, 79), (2, 99), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 95), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109149) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 89), (1, 79), (2, 99), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10914c) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 103), (1, 79), (2, 99), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10914f) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 105), (1, 79), (2, 99), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109153) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 105), (1, 79), (2, 107), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109156) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 109), (1, 79), (2, 107), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109159) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 111), (1, 79), (2, 107), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10915c) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 111), (1, 79), (2, 113), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10915f) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 111), (1, 79), (2, 115), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109163) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f32 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 111), (1, 79), (2, 117), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109166) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f33 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 111), (1, 79), (2, 117), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (15, 119), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109169) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f34 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 111), (1, 79), (2, 117), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (15, 121), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10916d) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f35 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 111), (1, 79), (2, 117), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109170) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f36 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 111), (1, 79), (2, 117), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109173) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f37 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 111), (1, 79), (2, 127), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109176) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.exec (n := 129) (ρ' := [(0, 111), (1, 79), (2, 127), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10917e) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f39 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 111), (1, 79), (2, 127), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 130), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109182) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1090e0_2 code

theorem rest_l1090e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1090e0 bytes_l1090e0) (entryMap (live .l1090e0))
      137 0x1090e0 bytes_l1090e0 b_l1090e0 := by
  have f0 : InstrSpec 0x1090e0 [0x48, 0x8B, 0x5C, 0x24, 0x08] (LoadPre 0x1090e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1090e0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090e0 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1090e0 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1090e0 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1090e5 [0x4C, 0x8B, 0x5C, 0x24, 0x10] (LoadPre 0x1090e5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1090e5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090e5 11 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1090e5 11 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1090e5 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1090ea [0x48, 0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x1090ea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1090ea + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090ea 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1090ea 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1090ea 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1090ef [0x48, 0x8B, 0x74, 0x24, 0x20] (LoadPre 0x1090ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1090ef + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090ef 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1090ef 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1090ef 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1090f4 [0x4C, 0x8B, 0x54, 0x24, 0x28] (LoadPre 0x1090f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1090f4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090f4 10 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1090f4 10 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1090f4 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1090f9 [0x4C, 0x8B, 0x64, 0x24, 0x30] (LoadPre 0x1090f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1090f9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090f9 12 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x1090f9 12 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1090f9 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1090fe [0x4C, 0x8B, 0x74, 0x24, 0x38] (LoadPre 0x1090fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1090fe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090fe 14 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x1090fe 14 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1090fe 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x109103 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x109103) (movR64R64Effect 0x109103 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109103 0 3).toInstrSpec (mov_r64_r64_effect_step 0x109103 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x109106 [0x48, 0xC1, 0xC0, 0x28] (fun s => s.RIP = 0x109106) (rolR64Effect 0x109106 4 0 40)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x109106 4 0 40).toInstrSpec (rol_r64_imm8_effect_step 0x109106 0x48 0xc0 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10910a [0x49, 0xBD, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00] (fun s => s.RIP = 0x10910a) (movR64Imm64Effect 0x10910a 13 0xff00ff00ff00ff)
      [] [] [.reg 13, .rip] :=
    (movR64Imm64Effect_footprint 0x10910a 13 0xff00ff00ff00ff).toInstrSpec (mov_r64_imm64_effect_step 0x10910a 0x49 0xbd (by decide) (by decide) 0xff00ff00ff00ff) pre_rip
  have f10 : InstrSpec 0x109114 [0x4C, 0x21, 0xE8] (fun s => s.RIP = 0x109114) (andR64R64Effect 0x109114 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109114 0 13).toInstrSpec (and_r64_r64_effect_step 0x109114 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x109117 [0x49, 0x89, 0xD9] (fun s => s.RIP = 0x109117) (movR64R64Effect 0x109117 9 3)
      [.gpr 3] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x109117 9 3).toInstrSpec (mov_r64_r64_effect_step 0x109117 0x49 0xd9 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10911a [0x49, 0xC1, 0xC1, 0x38] (fun s => s.RIP = 0x10911a) (rolR64Effect 0x10911a 4 9 56)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (rolR64Effect_footprint 0x10911a 4 9 56).toInstrSpec (rol_r64_imm8_effect_step 0x10911a 0x49 0xc1 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10911e [0x48, 0xB9, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF] (fun s => s.RIP = 0x10911e) (movR64Imm64Effect 0x10911e 1 0xff00ff00ff00ff00)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10911e 1 0xff00ff00ff00ff00).toInstrSpec (mov_r64_imm64_effect_step 0x10911e 0x48 0xb9 (by decide) (by decide) 0xff00ff00ff00ff00) pre_rip
  have f14 : InstrSpec 0x109128 [0x49, 0x21, 0xC9] (fun s => s.RIP = 0x109128) (andR64R64Effect 0x109128 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109128 9 1).toInstrSpec (and_r64_r64_effect_step 0x109128 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10912b [0x49, 0x09, 0xC1] (fun s => s.RIP = 0x10912b) (orR64R64Effect 0x10912b 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10912b 9 0).toInstrSpec (or_r64_r64_effect_step 0x10912b 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10912e [0x4C, 0x89, 0xD8] (fun s => s.RIP = 0x10912e) (movR64R64Effect 0x10912e 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10912e 0 11).toInstrSpec (mov_r64_r64_effect_step 0x10912e 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x109131 [0x48, 0xC1, 0xC0, 0x28] (fun s => s.RIP = 0x109131) (rolR64Effect 0x109131 4 0 40)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x109131 4 0 40).toInstrSpec (rol_r64_imm8_effect_step 0x109131 0x48 0xc0 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x109135 [0x4C, 0x21, 0xE8] (fun s => s.RIP = 0x109135) (andR64R64Effect 0x109135 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109135 0 13).toInstrSpec (and_r64_r64_effect_step 0x109135 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x109138 [0x4D, 0x89, 0xD8] (fun s => s.RIP = 0x109138) (movR64R64Effect 0x109138 8 11)
      [.gpr 11] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x109138 8 11).toInstrSpec (mov_r64_r64_effect_step 0x109138 0x4d 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090e5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (11, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090ea) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 53), (4, 4), (5, 5), (7, 57), (11, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090ef) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (11, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090f4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (10, 61), (11, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090f9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (10, 61), (11, 55), (12, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090fe) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (10, 61), (11, 55), (12, 63), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109103) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (10, 61), (11, 55), (12, 63), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109106) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (10, 61), (11, 55), (12, 63), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10910a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109114) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109117) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 73), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 75), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10911a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 73), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 77), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10911e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 73), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 77), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109128) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 73), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 81), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10912b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 73), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10912e) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109131) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109135) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 89), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109138) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 89), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 91), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10913b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1090e0_1 code

theorem block_l1090e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1090e0 :=
  Rest.liftedBlock (rest_l1090e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1090e0 x hx)

theorem rest_l109326 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109326 bytes_l109326) (entryMap (live .l109326))
      2 0x109326 bytes_l109326 b_l109326 := by
  have f0 : InstrSpec 0x109326 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x109326) (movR64R64Effect 0x109326 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x109326 7 3).toInstrSpec (mov_r64_r64_effect_step 0x109326 0x48 0xdf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x109329 [0xE8, 0x02, 0x75, 0xFF, 0xFF] (PushPre 0x109329 5) (callEffect (fun _ => 0x100830) 0x10932e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109329 0x100830 0x10932e).toInstrSpec (call_rel32_effect_step 0x109329 0xffff7502 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109329) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100830) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l109326 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109326 :=
  Rest.liftedBlock (rest_l109326 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109326 x hx)

theorem rest_l10932e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10932e bytes_l10932e) (entryMap (live .l10932e))
      19 0x10932e bytes_l10932e b_l10932e := by
  have f0 : InstrSpec 0x10932e [0x48, 0x8B, 0x84, 0xEC, 0xD8, 0x01, 0x00, 0x00] (LoadPre 0x10932e (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1d8)) s (0x10932e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10932e 0 (.sib 4 (some 5) 3 (.d32 0x1d8)))
      [.gpr 4, .gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10932e 0 (.sib 4 (some 5) 3 (.d32 0x1d8))).toInstrSpec (mov_r64_m64_effect_step 0x10932e 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x1d8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x109336 [0x48, 0x31, 0x44, 0x24, 0x08] (StorePre 0x109336 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109336 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x109336 5 64 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x109336 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (xor_m64_r64_effect_step 0x109336 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10933b [0x48, 0x8B, 0x84, 0xEC, 0xE0, 0x01, 0x00, 0x00] (LoadPre 0x10933b (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1e0)) s (0x10933b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10933b 0 (.sib 4 (some 5) 3 (.d32 0x1e0)))
      [.gpr 4, .gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10933b 0 (.sib 4 (some 5) 3 (.d32 0x1e0))).toInstrSpec (mov_r64_m64_effect_step 0x10933b 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x1e0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x109343 [0x48, 0x31, 0x44, 0x24, 0x10] (StorePre 0x109343 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109343 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x109343 5 64 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x109343 5 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (xor_m64_r64_effect_step 0x109343 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x109348 [0x48, 0x8B, 0x84, 0xEC, 0xE8, 0x01, 0x00, 0x00] (LoadPre 0x109348 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1e8)) s (0x109348 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109348 0 (.sib 4 (some 5) 3 (.d32 0x1e8)))
      [.gpr 4, .gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109348 0 (.sib 4 (some 5) 3 (.d32 0x1e8))).toInstrSpec (mov_r64_m64_effect_step 0x109348 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x1e8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x109350 [0x48, 0x31, 0x44, 0x24, 0x18] (StorePre 0x109350 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109350 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x109350 5 64 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x109350 5 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (xor_m64_r64_effect_step 0x109350 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x109355 [0x48, 0x8B, 0x84, 0xEC, 0xF0, 0x01, 0x00, 0x00] (LoadPre 0x109355 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1f0)) s (0x109355 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109355 0 (.sib 4 (some 5) 3 (.d32 0x1f0)))
      [.gpr 4, .gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109355 0 (.sib 4 (some 5) 3 (.d32 0x1f0))).toInstrSpec (mov_r64_m64_effect_step 0x109355 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x1f0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10935d [0x48, 0x31, 0x44, 0x24, 0x20] (StorePre 0x10935d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10935d + BitVec.ofNat 64 5)) 8) (xorMREffect 0x10935d 5 64 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x10935d 5 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (xor_m64_r64_effect_step 0x10935d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x109362 [0x48, 0x8B, 0x84, 0xEC, 0xF8, 0x01, 0x00, 0x00] (LoadPre 0x109362 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1f8)) s (0x109362 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109362 0 (.sib 4 (some 5) 3 (.d32 0x1f8)))
      [.gpr 4, .gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109362 0 (.sib 4 (some 5) 3 (.d32 0x1f8))).toInstrSpec (mov_r64_m64_effect_step 0x109362 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x1f8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10936a [0x48, 0x31, 0x44, 0x24, 0x28] (StorePre 0x10936a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10936a + BitVec.ofNat 64 5)) 8) (xorMREffect 0x10936a 5 64 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x10936a 5 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (xor_m64_r64_effect_step 0x10936a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10936f [0x48, 0x8B, 0x84, 0xEC, 0x00, 0x02, 0x00, 0x00] (LoadPre 0x10936f (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x200)) s (0x10936f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10936f 0 (.sib 4 (some 5) 3 (.d32 0x200)))
      [.gpr 4, .gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10936f 0 (.sib 4 (some 5) 3 (.d32 0x200))).toInstrSpec (mov_r64_m64_effect_step 0x10936f 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x200)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x109377 [0x48, 0x31, 0x44, 0x24, 0x30] (StorePre 0x109377 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109377 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x109377 5 64 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x109377 5 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (xor_m64_r64_effect_step 0x109377 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10937c [0x48, 0x8B, 0x84, 0xEC, 0x08, 0x02, 0x00, 0x00] (LoadPre 0x10937c (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x208)) s (0x10937c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10937c 0 (.sib 4 (some 5) 3 (.d32 0x208)))
      [.gpr 4, .gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10937c 0 (.sib 4 (some 5) 3 (.d32 0x208))).toInstrSpec (mov_r64_m64_effect_step 0x10937c 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x208)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x109384 [0x48, 0x31, 0x44, 0x24, 0x38] (StorePre 0x109384 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109384 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x109384 5 64 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x109384 5 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (xor_m64_r64_effect_step 0x109384 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x109389 [0x48, 0x8B, 0x84, 0xEC, 0x10, 0x02, 0x00, 0x00] (LoadPre 0x109389 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x210)) s (0x109389 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109389 0 (.sib 4 (some 5) 3 (.d32 0x210)))
      [.gpr 4, .gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109389 0 (.sib 4 (some 5) 3 (.d32 0x210))).toInstrSpec (mov_r64_m64_effect_step 0x109389 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x210)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x109391 [0x48, 0x31, 0x44, 0x24, 0x40] (StorePre 0x109391 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x109391 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x109391 5 64 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x109391 5 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (xor_m64_r64_effect_step 0x109391 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x109396 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109396) (movR32Imm32Effect 0x109396 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x109396 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x109396 0xbe (by decide) 0x8) pre_rip
  have f17 : InstrSpec 0x10939b [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x10939b) (movR64R64Effect 0x10939b 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10939b 7 3).toInstrSpec (mov_r64_r64_effect_step 0x10939b 0x48 0xdf (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10939e [0xE8, 0xED, 0x7A, 0xFF, 0xFF] (PushPre 0x10939e 5) (callEffect (fun _ => 0x100e90) 0x1093a3)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10939e 0x100e90 0x1093a3).toInstrSpec (call_rel32_effect_step 0x10939e 0xffff7aed (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109336) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10933b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109343) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109348) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109350) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109355) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10935d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109362) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10936a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10936f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109377) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10937c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109384) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109389) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109391) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109396) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (6, 77), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10939b) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (6, 77), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10939e) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 74), (3, 3), (4, 81), (5, 5), (6, 77), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e90) f18 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 83) (by decide) (by decide) rfl rfl

theorem block_l10932e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10932e :=
  Rest.liftedBlock (rest_l10932e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10932e x hx)

theorem rest_l1093a3_4 [Bindings] (code : CodeMap) :
    Rest (n := 204) code lifted (codeRange 0x1093a3 bytes_l1093a3) [(0, 195), (1, 199), (2, 184), (3, 202), (4, 4), (5, 5), (6, 177), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x1094ec bytes_l1093a3_4 b_l1093a3_4 := by
  have f80 : InstrSpec 0x1094ec [0x48, 0xC1, 0xC7, 0x20] (fun s => s.RIP = 0x1094ec) (rolR64Effect 0x1094ec 4 7 32)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (rolR64Effect_footprint 0x1094ec 4 7 32).toInstrSpec (rol_r64_imm8_effect_step 0x1094ec 0x48 0xc7 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x1094f0 [0x48, 0x33, 0xBC, 0xEC, 0x48, 0x02, 0x00, 0x00] (LoadPre 0x1094f0 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x248)) s (0x1094f0 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x1094f0 7 (.sib 4 (some 5) 3 (.d32 0x248)))
      [.gpr 7, .gpr 4, .gpr 5] [] [.reg 7, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x1094f0 7 (.sib 4 (some 5) 3 (.d32 0x248))).toInstrSpec (xor_r64_m64_effect_step 0x1094f0 0x48 (by decide) 7 (.sib 4 (some 5) 3 (.d32 0x248)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f82 : InstrSpec 0x1094f8 [0x48, 0x31, 0xFB] (fun s => s.RIP = 0x1094f8) (xorR64R64Effect 0x1094f8 3 7)
      [.gpr 3, .gpr 7] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1094f8 3 7).toInstrSpec (xor_r64_r64_effect_step 0x1094f8 0x48 0xfb (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x1094fb [0x48, 0x89, 0x5C, 0x24, 0x38] (StorePre 0x1094fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1094fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1094fb 3 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1094fb 3 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x1094fb 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f84 : InstrSpec 0x109500 [0x48, 0x83, 0xC5, 0x20] (fun s => s.RIP = 0x109500) (addR64Imm8Effect 0x109500 5 0x20)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x109500 5 0x20).toInstrSpec (add_r64_imm8_effect_step 0x109500 0x48 0xc5 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f80 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 195), (1, 199), (2, 184), (3, 202), (4, 4), (5, 5), (6, 177), (7, 204), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094f0) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f81 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 195), (1, 199), (2, 184), (3, 202), (4, 4), (5, 5), (6, 177), (7, 206), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094f8) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f82 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 195), (1, 199), (2, 184), (3, 208), (4, 4), (5, 5), (6, 177), (7, 206), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094fb) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.exec (n := 210) (ρ' := [(0, 195), (1, 199), (2, 184), (3, 208), (4, 4), (5, 5), (6, 177), (7, 206), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109500) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 211) (RestInside.out (n := 211) f84 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 212) (ρ' := [(0, 195), (1, 199), (2, 184), (3, 208), (4, 4), (5, 211), (6, 177), (7, 206), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109504) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 213) (jmp_rel32_effect_step 0x109504 0xfffffb07 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l1093a3_3 [Bindings] (code : CodeMap) :
    Rest (n := 168) code lifted (codeRange 0x1093a3 bytes_l1093a3) [(0, 139), (1, 115), (2, 137), (3, 151), (4, 4), (5, 5), (6, 117), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]
      26 0x109495 bytes_l1093a3_3 b_l1093a3_3 := by
  have f60 : InstrSpec 0x109495 [0x4C, 0x89, 0x44, 0x24, 0x18] (StorePre 0x109495 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109495 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109495 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109495 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x109495 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f61 : InstrSpec 0x10949a [0x48, 0xC1, 0xC6, 0x20] (fun s => s.RIP = 0x10949a) (rolR64Effect 0x10949a 4 6 32)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR64Effect_footprint 0x10949a 4 6 32).toInstrSpec (rol_r64_imm8_effect_step 0x10949a 0x48 0xc6 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x10949e [0x48, 0x33, 0xB4, 0xEC, 0x30, 0x02, 0x00, 0x00] (LoadPre 0x10949e (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x230)) s (0x10949e + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x10949e 6 (.sib 4 (some 5) 3 (.d32 0x230)))
      [.gpr 6, .gpr 4, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x10949e 6 (.sib 4 (some 5) 3 (.d32 0x230))).toInstrSpec (xor_r64_m64_effect_step 0x10949e 0x48 (by decide) 6 (.sib 4 (some 5) 3 (.d32 0x230)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f63 : InstrSpec 0x1094a6 [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x1094a6) (xorR64R64Effect 0x1094a6 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1094a6 2 6).toInstrSpec (xor_r64_r64_effect_step 0x1094a6 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x1094a9 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x1094a9) (movR64R64Effect 0x1094a9 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1094a9 6 3).toInstrSpec (mov_r64_r64_effect_step 0x1094a9 0x48 0xde (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x1094ac [0x48, 0xC1, 0xC6, 0x30] (fun s => s.RIP = 0x1094ac) (rolR64Effect 0x1094ac 4 6 48)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR64Effect_footprint 0x1094ac 4 6 48).toInstrSpec (rol_r64_imm8_effect_step 0x1094ac 0x48 0xc6 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x1094b0 [0x48, 0x89, 0x54, 0x24, 0x20] (StorePre 0x1094b0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1094b0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1094b0 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1094b0 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1094b0 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f67 : InstrSpec 0x1094b5 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x1094b5) (movR64R64Effect 0x1094b5 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1094b5 2 1).toInstrSpec (mov_r64_r64_effect_step 0x1094b5 0x48 0xca (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x1094b8 [0x48, 0xC1, 0xC2, 0x20] (fun s => s.RIP = 0x1094b8) (rolR64Effect 0x1094b8 4 2 32)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR64Effect_footprint 0x1094b8 4 2 32).toInstrSpec (rol_r64_imm8_effect_step 0x1094b8 0x48 0xc2 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x1094bc [0x48, 0x33, 0x94, 0xEC, 0x38, 0x02, 0x00, 0x00] (LoadPre 0x1094bc (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x238)) s (0x1094bc + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x1094bc 2 (.sib 4 (some 5) 3 (.d32 0x238)))
      [.gpr 2, .gpr 4, .gpr 5] [] [.reg 2, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x1094bc 2 (.sib 4 (some 5) 3 (.d32 0x238))).toInstrSpec (xor_r64_m64_effect_step 0x1094bc 0x48 (by decide) 2 (.sib 4 (some 5) 3 (.d32 0x238)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f70 : InstrSpec 0x1094c4 [0x48, 0x31, 0xD0] (fun s => s.RIP = 0x1094c4) (xorR64R64Effect 0x1094c4 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1094c4 0 2).toInstrSpec (xor_r64_r64_effect_step 0x1094c4 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x1094c7 [0x48, 0x31, 0xF3] (fun s => s.RIP = 0x1094c7) (xorR64R64Effect 0x1094c7 3 6)
      [.gpr 3, .gpr 6] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1094c7 3 6).toInstrSpec (xor_r64_r64_effect_step 0x1094c7 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x1094ca [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x1094ca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1094ca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1094ca 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1094ca 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1094ca 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f73 : InstrSpec 0x1094cf [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1094cf) (movR64R64Effect 0x1094cf 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1094cf 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1094cf 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x1094d2 [0x48, 0xC1, 0xC0, 0x20] (fun s => s.RIP = 0x1094d2) (rolR64Effect 0x1094d2 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x1094d2 4 0 32).toInstrSpec (rol_r64_imm8_effect_step 0x1094d2 0x48 0xc0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x1094d6 [0x48, 0x33, 0x84, 0xEC, 0x40, 0x02, 0x00, 0x00] (LoadPre 0x1094d6 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x240)) s (0x1094d6 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x1094d6 0 (.sib 4 (some 5) 3 (.d32 0x240)))
      [.gpr 0, .gpr 4, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x1094d6 0 (.sib 4 (some 5) 3 (.d32 0x240))).toInstrSpec (xor_r64_m64_effect_step 0x1094d6 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x240)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f76 : InstrSpec 0x1094de [0x48, 0x31, 0xF1] (fun s => s.RIP = 0x1094de) (xorR64R64Effect 0x1094de 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1094de 1 6).toInstrSpec (xor_r64_r64_effect_step 0x1094de 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x1094e1 [0x48, 0x31, 0xC1] (fun s => s.RIP = 0x1094e1) (xorR64R64Effect 0x1094e1 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1094e1 1 0).toInstrSpec (xor_r64_r64_effect_step 0x1094e1 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x1094e4 [0x48, 0x89, 0x4C, 0x24, 0x30] (StorePre 0x1094e4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1094e4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1094e4 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1094e4 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1094e4 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f79 : InstrSpec 0x1094e9 [0x4C, 0x31, 0xDB] (fun s => s.RIP = 0x1094e9) (xorR64R64Effect 0x1094e9 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1094e9 3 11).toInstrSpec (xor_r64_r64_effect_step 0x1094e9 0x4c 0xdb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 168) (RestInside.exec (n := 168) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 151), (4, 4), (5, 5), (6, 117), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10949a) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f61 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 151), (4, 4), (5, 5), (6, 169), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10949e) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f62 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 151), (4, 4), (5, 5), (6, 171), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094a6) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f63 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 139), (1, 115), (2, 173), (3, 151), (4, 4), (5, 5), (6, 171), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094a9) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f64 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 139), (1, 115), (2, 173), (3, 151), (4, 4), (5, 5), (6, 175), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094ac) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f65 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 139), (1, 115), (2, 173), (3, 151), (4, 4), (5, 5), (6, 177), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094b0) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.exec (n := 179) (ρ' := [(0, 139), (1, 115), (2, 173), (3, 151), (4, 4), (5, 5), (6, 177), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094b5) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f67 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(0, 139), (1, 115), (2, 180), (3, 151), (4, 4), (5, 5), (6, 177), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094b8) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f68 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 139), (1, 115), (2, 182), (3, 151), (4, 4), (5, 5), (6, 177), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094bc) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f69 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(0, 139), (1, 115), (2, 184), (3, 151), (4, 4), (5, 5), (6, 177), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094c4) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 186) (RestInside.out (n := 186) f70 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 187) (ρ' := [(0, 186), (1, 115), (2, 184), (3, 151), (4, 4), (5, 5), (6, 177), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094c7) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 188) (RestInside.out (n := 188) f71 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 189) (ρ' := [(0, 186), (1, 115), (2, 184), (3, 188), (4, 4), (5, 5), (6, 177), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094ca) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 190) (RestInside.exec (n := 190) (ρ' := [(0, 186), (1, 115), (2, 184), (3, 188), (4, 4), (5, 5), (6, 177), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094cf) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f73 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 191), (1, 115), (2, 184), (3, 188), (4, 4), (5, 5), (6, 177), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094d2) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f74 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 193), (1, 115), (2, 184), (3, 188), (4, 4), (5, 5), (6, 177), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094d6) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f75 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 195), (1, 115), (2, 184), (3, 188), (4, 4), (5, 5), (6, 177), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094de) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f76 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 195), (1, 197), (2, 184), (3, 188), (4, 4), (5, 5), (6, 177), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094e1) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f77 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 195), (1, 199), (2, 184), (3, 188), (4, 4), (5, 5), (6, 177), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094e4) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.exec (n := 201) (ρ' := [(0, 195), (1, 199), (2, 184), (3, 188), (4, 4), (5, 5), (6, 177), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094e9) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f79 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 195), (1, 199), (2, 184), (3, 202), (4, 4), (5, 5), (6, 177), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094ec) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1093a3_4 code

theorem rest_l1093a3_2 [Bindings] (code : CodeMap) :
    Rest (n := 131) code lifted (codeRange 0x1093a3 bytes_l1093a3) [(0, 119), (1, 115), (2, 109), (3, 127), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 105), (10, 61), (11, 121), (12, 125), (13, 107), (14, 129), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]
      46 0x10943a bytes_l1093a3_2 b_l1093a3_2 := by
  have f40 : InstrSpec 0x10943a [0x49, 0xC1, 0xC6, 0x20] (fun s => s.RIP = 0x10943a) (rolR64Effect 0x10943a 4 14 32)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (rolR64Effect_footprint 0x10943a 4 14 32).toInstrSpec (rol_r64_imm8_effect_step 0x10943a 0x49 0xc6 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x10943e [0x49, 0x31, 0xDA] (fun s => s.RIP = 0x10943e) (xorR64R64Effect 0x10943e 10 3)
      [.gpr 10, .gpr 3] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10943e 10 3).toInstrSpec (xor_r64_r64_effect_step 0x10943e 0x49 0xda (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x109441 [0x49, 0x31, 0xD9] (fun s => s.RIP = 0x109441) (xorR64R64Effect 0x109441 9 3)
      [.gpr 9, .gpr 3] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109441 9 3).toInstrSpec (xor_r64_r64_effect_step 0x109441 0x49 0xd9 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x109444 [0x48, 0x31, 0xDA] (fun s => s.RIP = 0x109444) (xorR64R64Effect 0x109444 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109444 2 3).toInstrSpec (xor_r64_r64_effect_step 0x109444 0x48 0xda (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x109447 [0x48, 0x31, 0xD8] (fun s => s.RIP = 0x109447) (xorR64R64Effect 0x109447 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109447 0 3).toInstrSpec (xor_r64_r64_effect_step 0x109447 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x10944a [0x48, 0xC1, 0xC3, 0x20] (fun s => s.RIP = 0x10944a) (rolR64Effect 0x10944a 4 3 32)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (rolR64Effect_footprint 0x10944a 4 3 32).toInstrSpec (rol_r64_imm8_effect_step 0x10944a 0x48 0xc3 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x10944e [0x49, 0x31, 0xFF] (fun s => s.RIP = 0x10944e) (xorR64R64Effect 0x10944e 15 7)
      [.gpr 15, .gpr 7] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10944e 15 7).toInstrSpec (xor_r64_r64_effect_step 0x10944e 0x49 0xff (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x109451 [0x49, 0x31, 0xDF] (fun s => s.RIP = 0x109451) (xorR64R64Effect 0x109451 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109451 15 3).toInstrSpec (xor_r64_r64_effect_step 0x109451 0x49 0xdf (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x109454 [0x4C, 0x33, 0xA4, 0xEC, 0x18, 0x02, 0x00, 0x00] (LoadPre 0x109454 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x218)) s (0x109454 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109454 12 (.sib 4 (some 5) 3 (.d32 0x218)))
      [.gpr 12, .gpr 4, .gpr 5] [] [.reg 12, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x109454 12 (.sib 4 (some 5) 3 (.d32 0x218))).toInstrSpec (xor_r64_m64_effect_step 0x109454 0x4c (by decide) 4 (.sib 4 (some 5) 3 (.d32 0x218)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f49 : InstrSpec 0x10945c [0x4D, 0x31, 0xE2] (fun s => s.RIP = 0x10945c) (xorR64R64Effect 0x10945c 10 12)
      [.gpr 10, .gpr 12] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10945c 10 12).toInstrSpec (xor_r64_r64_effect_step 0x10945c 0x4d 0xe2 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x10945f [0x48, 0x8B, 0x5C, 0x24, 0x30] (LoadPre 0x10945f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10945f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10945f 3 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x10945f 3 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10945f 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f51 : InstrSpec 0x109464 [0x4C, 0x89, 0x7C, 0x24, 0x40] (StorePre 0x109464 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x109464 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109464 15 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109464 15 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x109464 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x109469 [0x4C, 0x33, 0xB4, 0xEC, 0x20, 0x02, 0x00, 0x00] (LoadPre 0x109469 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x220)) s (0x109469 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109469 14 (.sib 4 (some 5) 3 (.d32 0x220)))
      [.gpr 14, .gpr 4, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x109469 14 (.sib 4 (some 5) 3 (.d32 0x220))).toInstrSpec (xor_r64_m64_effect_step 0x109469 0x4c (by decide) 6 (.sib 4 (some 5) 3 (.d32 0x220)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f53 : InstrSpec 0x109471 [0x4C, 0x89, 0x54, 0x24, 0x08] (StorePre 0x109471 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109471 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109471 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109471 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109471 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x109476 [0x4D, 0x31, 0xF1] (fun s => s.RIP = 0x109476) (xorR64R64Effect 0x109476 9 14)
      [.gpr 9, .gpr 14] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109476 9 14).toInstrSpec (xor_r64_r64_effect_step 0x109476 0x4d 0xf1 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x109479 [0x4C, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x109479 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109479 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109479 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109479 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x109479 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x10947e [0x4C, 0x33, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x10947e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10947e + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x10947e 8 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 8, .gpr 4] [] [.reg 8, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x10947e 8 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (xor_r64_m64_effect_step 0x10947e 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f57 : InstrSpec 0x109486 [0x49, 0xC1, 0xC5, 0x20] (fun s => s.RIP = 0x109486) (rolR64Effect 0x109486 4 13 32)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (rolR64Effect_footprint 0x109486 4 13 32).toInstrSpec (rol_r64_imm8_effect_step 0x109486 0x49 0xc5 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x10948a [0x4C, 0x33, 0xAC, 0xEC, 0x28, 0x02, 0x00, 0x00] (LoadPre 0x10948a (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x228)) s (0x10948a + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x10948a 13 (.sib 4 (some 5) 3 (.d32 0x228)))
      [.gpr 13, .gpr 4, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x10948a 13 (.sib 4 (some 5) 3 (.d32 0x228))).toInstrSpec (xor_r64_m64_effect_step 0x10948a 0x4c (by decide) 5 (.sib 4 (some 5) 3 (.d32 0x228)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f59 : InstrSpec 0x109492 [0x4D, 0x31, 0xE8] (fun s => s.RIP = 0x109492) (xorR64R64Effect 0x109492 8 13)
      [.gpr 8, .gpr 13] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109492 8 13).toInstrSpec (xor_r64_r64_effect_step 0x109492 0x4d 0xe8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f40 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 119), (1, 115), (2, 109), (3, 127), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 105), (10, 61), (11, 121), (12, 125), (13, 107), (14, 131), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10943e) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f41 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 119), (1, 115), (2, 109), (3, 127), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 105), (10, 133), (11, 121), (12, 125), (13, 107), (14, 131), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109441) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f42 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 119), (1, 115), (2, 109), (3, 127), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 135), (10, 133), (11, 121), (12, 125), (13, 107), (14, 131), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109444) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f43 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 119), (1, 115), (2, 137), (3, 127), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 135), (10, 133), (11, 121), (12, 125), (13, 107), (14, 131), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109447) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f44 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 127), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 135), (10, 133), (11, 121), (12, 125), (13, 107), (14, 131), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10944a) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f45 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 141), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 135), (10, 133), (11, 121), (12, 125), (13, 107), (14, 131), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10944e) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f46 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 141), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 135), (10, 133), (11, 121), (12, 125), (13, 107), (14, 131), (15, 143), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109451) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f47 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 141), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 135), (10, 133), (11, 121), (12, 125), (13, 107), (14, 131), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109454) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f48 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 141), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 135), (10, 133), (11, 121), (12, 147), (13, 107), (14, 131), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10945c) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f49 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 141), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 135), (10, 149), (11, 121), (12, 147), (13, 107), (14, 131), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10945f) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f50 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 151), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 135), (10, 149), (11, 121), (12, 147), (13, 107), (14, 131), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109464) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.exec (n := 153) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 151), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 135), (10, 149), (11, 121), (12, 147), (13, 107), (14, 131), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109469) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f52 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 151), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 135), (10, 149), (11, 121), (12, 147), (13, 107), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109471) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.exec (n := 156) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 151), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 135), (10, 149), (11, 121), (12, 147), (13, 107), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109476) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f54 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 151), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 157), (10, 149), (11, 121), (12, 147), (13, 107), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109479) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.exec (n := 159) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 151), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 157), (10, 149), (11, 121), (12, 147), (13, 107), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10947e) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f56 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 151), (4, 4), (5, 5), (6, 117), (7, 123), (8, 160), (9, 157), (10, 149), (11, 121), (12, 147), (13, 107), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109486) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f57 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 151), (4, 4), (5, 5), (6, 117), (7, 123), (8, 160), (9, 157), (10, 149), (11, 121), (12, 147), (13, 162), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10948a) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f58 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 151), (4, 4), (5, 5), (6, 117), (7, 123), (8, 160), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109492) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f59 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 139), (1, 115), (2, 137), (3, 151), (4, 4), (5, 5), (6, 117), (7, 123), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109495) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1093a3_3 code

theorem rest_l1093a3_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x1093a3 bytes_l1093a3) [(0, 63), (1, 69), (2, 57), (3, 84), (4, 4), (5, 5), (6, 90), (7, 78), (8, 55), (9, 53), (10, 61), (11, 75), (13, 67), (14, 88), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]
      66 0x1093f7 bytes_l1093a3_1 b_l1093a3_1 := by
  have f20 : InstrSpec 0x1093f7 [0x48, 0xC1, 0xC6, 0x30] (fun s => s.RIP = 0x1093f7) (rolR64Effect 0x1093f7 4 6 48)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR64Effect_footprint 0x1093f7 4 6 48).toInstrSpec (rol_r64_imm8_effect_step 0x1093f7 0x48 0xc6 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x1093fb [0x48, 0x89, 0x74, 0x24, 0x78] (StorePre 0x1093fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1093fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1093fb 6 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1093fb 6 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x1093fb 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x109400 [0x4D, 0x31, 0xD1] (fun s => s.RIP = 0x109400) (xorR64R64Effect 0x109400 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109400 9 10).toInstrSpec (xor_r64_r64_effect_step 0x109400 0x4d 0xd1 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x109403 [0x4D, 0x31, 0xE8] (fun s => s.RIP = 0x109403) (xorR64R64Effect 0x109403 8 13)
      [.gpr 8, .gpr 13] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109403 8 13).toInstrSpec (xor_r64_r64_effect_step 0x109403 0x4d 0xe8 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x109406 [0x4C, 0x31, 0xDA] (fun s => s.RIP = 0x109406) (xorR64R64Effect 0x109406 2 11)
      [.gpr 2, .gpr 11] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109406 2 11).toInstrSpec (xor_r64_r64_effect_step 0x109406 0x4c 0xda (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x109409 [0x4C, 0x31, 0xF8] (fun s => s.RIP = 0x109409) (xorR64R64Effect 0x109409 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109409 0 15).toInstrSpec (xor_r64_r64_effect_step 0x109409 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10940c [0x4D, 0x89, 0xCC] (fun s => s.RIP = 0x10940c) (movR64R64Effect 0x10940c 12 9)
      [.gpr 9] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10940c 12 9).toInstrSpec (mov_r64_r64_effect_step 0x10940c 0x4d 0xcc (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x10940f [0x4D, 0x31, 0xE9] (fun s => s.RIP = 0x10940f) (xorR64R64Effect 0x10940f 9 13)
      [.gpr 9, .gpr 13] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10940f 9 13).toInstrSpec (xor_r64_r64_effect_step 0x10940f 0x4d 0xe9 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x109412 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x109412) (movR64R64Effect 0x109412 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x109412 13 2).toInstrSpec (mov_r64_r64_effect_step 0x109412 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x109415 [0x4C, 0x31, 0xFA] (fun s => s.RIP = 0x109415) (xorR64R64Effect 0x109415 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109415 2 15).toInstrSpec (xor_r64_r64_effect_step 0x109415 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x109418 [0x49, 0x89, 0xDF] (fun s => s.RIP = 0x109418) (movR64R64Effect 0x109418 15 3)
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x109418 15 3).toInstrSpec (mov_r64_r64_effect_step 0x109418 0x49 0xdf (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x10941b [0x49, 0xC1, 0xC7, 0x30] (fun s => s.RIP = 0x10941b) (rolR64Effect 0x10941b 4 15 48)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR64Effect_footprint 0x10941b 4 15 48).toInstrSpec (rol_r64_imm8_effect_step 0x10941b 0x49 0xc7 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10941f [0x4C, 0x31, 0xF1] (fun s => s.RIP = 0x10941f) (xorR64R64Effect 0x10941f 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10941f 1 14).toInstrSpec (xor_r64_r64_effect_step 0x10941f 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x109422 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x109422) (movR64R64Effect 0x109422 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x109422 6 0).toInstrSpec (mov_r64_r64_effect_step 0x109422 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x109425 [0x4C, 0x31, 0xF0] (fun s => s.RIP = 0x109425) (xorR64R64Effect 0x109425 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109425 0 14).toInstrSpec (xor_r64_r64_effect_step 0x109425 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x109428 [0x4C, 0x8B, 0x5C, 0x24, 0x78] (LoadPre 0x109428 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109428 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109428 11 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x109428 11 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x109428 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x10942d [0x4C, 0x31, 0xDF] (fun s => s.RIP = 0x10942d) (xorR64R64Effect 0x10942d 7 11)
      [.gpr 7, .gpr 11] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10942d 7 11).toInstrSpec (xor_r64_r64_effect_step 0x10942d 0x4c 0xdf (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x109430 [0x49, 0xC1, 0xC4, 0x20] (fun s => s.RIP = 0x109430) (rolR64Effect 0x109430 4 12 32)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (rolR64Effect_footprint 0x109430 4 12 32).toInstrSpec (rol_r64_imm8_effect_step 0x109430 0x49 0xc4 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x109434 [0x4C, 0x31, 0xFB] (fun s => s.RIP = 0x109434) (xorR64R64Effect 0x109434 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109434 3 15).toInstrSpec (xor_r64_r64_effect_step 0x109434 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x109437 [0x4D, 0x89, 0xC6] (fun s => s.RIP = 0x109437) (movR64R64Effect 0x109437 14 8)
      [.gpr 8] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x109437 14 8).toInstrSpec (mov_r64_r64_effect_step 0x109437 0x4d 0xc6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 63), (1, 69), (2, 57), (3, 84), (4, 4), (5, 5), (6, 92), (7, 78), (8, 55), (9, 53), (10, 61), (11, 75), (13, 67), (14, 88), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093fb) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 63), (1, 69), (2, 57), (3, 84), (4, 4), (5, 5), (6, 92), (7, 78), (8, 55), (9, 53), (10, 61), (11, 75), (13, 67), (14, 88), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109400) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 63), (1, 69), (2, 57), (3, 84), (4, 4), (5, 5), (6, 92), (7, 78), (8, 55), (9, 95), (10, 61), (11, 75), (13, 67), (14, 88), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109403) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 63), (1, 69), (2, 57), (3, 84), (4, 4), (5, 5), (6, 92), (7, 78), (8, 97), (9, 95), (10, 61), (11, 75), (13, 67), (14, 88), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109406) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 63), (1, 69), (2, 99), (3, 84), (4, 4), (5, 5), (6, 92), (7, 78), (8, 97), (9, 95), (10, 61), (11, 75), (13, 67), (14, 88), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109409) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f25 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 101), (1, 69), (2, 99), (3, 84), (4, 4), (5, 5), (6, 92), (7, 78), (8, 97), (9, 95), (10, 61), (11, 75), (13, 67), (14, 88), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10940c) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 101), (1, 69), (2, 99), (3, 84), (4, 4), (5, 5), (6, 92), (7, 78), (8, 97), (9, 95), (10, 61), (11, 75), (12, 103), (13, 67), (14, 88), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10940f) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 101), (1, 69), (2, 99), (3, 84), (4, 4), (5, 5), (6, 92), (7, 78), (8, 97), (9, 105), (10, 61), (11, 75), (12, 103), (13, 67), (14, 88), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109412) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f28 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 101), (1, 69), (2, 99), (3, 84), (4, 4), (5, 5), (6, 92), (7, 78), (8, 97), (9, 105), (10, 61), (11, 75), (12, 103), (13, 107), (14, 88), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109415) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f29 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 101), (1, 69), (2, 109), (3, 84), (4, 4), (5, 5), (6, 92), (7, 78), (8, 97), (9, 105), (10, 61), (11, 75), (12, 103), (13, 107), (14, 88), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109418) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f30 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 101), (1, 69), (2, 109), (3, 84), (4, 4), (5, 5), (6, 92), (7, 78), (8, 97), (9, 105), (10, 61), (11, 75), (12, 103), (13, 107), (14, 88), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10941b) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f31 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 101), (1, 69), (2, 109), (3, 84), (4, 4), (5, 5), (6, 92), (7, 78), (8, 97), (9, 105), (10, 61), (11, 75), (12, 103), (13, 107), (14, 88), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10941f) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f32 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 101), (1, 115), (2, 109), (3, 84), (4, 4), (5, 5), (6, 92), (7, 78), (8, 97), (9, 105), (10, 61), (11, 75), (12, 103), (13, 107), (14, 88), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109422) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f33 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 101), (1, 115), (2, 109), (3, 84), (4, 4), (5, 5), (6, 117), (7, 78), (8, 97), (9, 105), (10, 61), (11, 75), (12, 103), (13, 107), (14, 88), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109425) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f34 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 119), (1, 115), (2, 109), (3, 84), (4, 4), (5, 5), (6, 117), (7, 78), (8, 97), (9, 105), (10, 61), (11, 75), (12, 103), (13, 107), (14, 88), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109428) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f35 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 119), (1, 115), (2, 109), (3, 84), (4, 4), (5, 5), (6, 117), (7, 78), (8, 97), (9, 105), (10, 61), (11, 121), (12, 103), (13, 107), (14, 88), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10942d) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f36 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 119), (1, 115), (2, 109), (3, 84), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 105), (10, 61), (11, 121), (12, 103), (13, 107), (14, 88), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109430) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f37 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 119), (1, 115), (2, 109), (3, 84), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 105), (10, 61), (11, 121), (12, 125), (13, 107), (14, 88), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109434) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f38 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 119), (1, 115), (2, 109), (3, 127), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 105), (10, 61), (11, 121), (12, 125), (13, 107), (14, 88), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109437) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f39 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 119), (1, 115), (2, 109), (3, 127), (4, 4), (5, 5), (6, 117), (7, 123), (8, 97), (9, 105), (10, 61), (11, 121), (12, 125), (13, 107), (14, 129), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10943a) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1093a3_2 code

theorem rest_l1093a3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1093a3 bytes_l1093a3) (entryMap (live .l1093a3))
      86 0x1093a3 bytes_l1093a3 b_l1093a3 := by
  have f0 : InstrSpec 0x1093a3 [0x4C, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x1093a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1093a3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1093a3 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1093a3 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1093a3 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1093a8 [0x4C, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1093a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1093a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1093a8 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1093a8 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1093a8 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1093ad [0x48, 0x8B, 0x54, 0x24, 0x18] (LoadPre 0x1093ad (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1093ad + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1093ad 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1093ad 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1093ad 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1093b2 [0x4D, 0x89, 0xCA] (fun s => s.RIP = 0x1093b2) (movR64R64Effect 0x1093b2 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1093b2 10 9).toInstrSpec (mov_r64_r64_effect_step 0x1093b2 0x4d 0xca (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1093b5 [0x49, 0xC1, 0xC2, 0x30] (fun s => s.RIP = 0x1093b5) (rolR64Effect 0x1093b5 4 10 48)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR64Effect_footprint 0x1093b5 4 10 48).toInstrSpec (rol_r64_imm8_effect_step 0x1093b5 0x49 0xc2 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1093b9 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x1093b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1093b9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1093b9 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1093b9 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1093b9 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1093be [0x4D, 0x89, 0xC5] (fun s => s.RIP = 0x1093be) (movR64R64Effect 0x1093be 13 8)
      [.gpr 8] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1093be 13 8).toInstrSpec (mov_r64_r64_effect_step 0x1093be 0x4d 0xc5 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1093c1 [0x49, 0xC1, 0xC5, 0x30] (fun s => s.RIP = 0x1093c1) (rolR64Effect 0x1093c1 4 13 48)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (rolR64Effect_footprint 0x1093c1 4 13 48).toInstrSpec (rol_r64_imm8_effect_step 0x1093c1 0x49 0xc5 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1093c5 [0x48, 0x8B, 0x4C, 0x24, 0x28] (LoadPre 0x1093c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1093c5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1093c5 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1093c5 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1093c5 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1093ca [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x1093ca) (movR64R64Effect 0x1093ca 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1093ca 6 2).toInstrSpec (mov_r64_r64_effect_step 0x1093ca 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1093cd [0x48, 0xC1, 0xC6, 0x30] (fun s => s.RIP = 0x1093cd) (rolR64Effect 0x1093cd 4 6 48)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR64Effect_footprint 0x1093cd 4 6 48).toInstrSpec (rol_r64_imm8_effect_step 0x1093cd 0x48 0xc6 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1093d1 [0x49, 0x89, 0xF3] (fun s => s.RIP = 0x1093d1) (movR64R64Effect 0x1093d1 11 6)
      [.gpr 6] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x1093d1 11 6).toInstrSpec (mov_r64_r64_effect_step 0x1093d1 0x49 0xf3 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1093d4 [0x48, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x1093d4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1093d4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1093d4 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1093d4 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x1093d4 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1093dc [0x48, 0x8B, 0x7C, 0x24, 0x38] (LoadPre 0x1093dc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1093dc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1093dc 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1093dc 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1093dc 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1093e1 [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x1093e1) (movR64R64Effect 0x1093e1 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1093e1 15 0).toInstrSpec (mov_r64_r64_effect_step 0x1093e1 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1093e4 [0x49, 0xC1, 0xC7, 0x30] (fun s => s.RIP = 0x1093e4) (rolR64Effect 0x1093e4 4 15 48)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR64Effect_footprint 0x1093e4 4 15 48).toInstrSpec (rol_r64_imm8_effect_step 0x1093e4 0x49 0xc7 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1093e8 [0x48, 0x8B, 0x5C, 0x24, 0x40] (LoadPre 0x1093e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1093e8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1093e8 3 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1093e8 3 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1093e8 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x1093ed [0x49, 0x89, 0xCE] (fun s => s.RIP = 0x1093ed) (movR64R64Effect 0x1093ed 14 1)
      [.gpr 1] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1093ed 14 1).toInstrSpec (mov_r64_r64_effect_step 0x1093ed 0x49 0xce (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1093f0 [0x49, 0xC1, 0xC6, 0x30] (fun s => s.RIP = 0x1093f0) (rolR64Effect 0x1093f0 4 14 48)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (rolR64Effect_footprint 0x1093f0 4 14 48).toInstrSpec (rol_r64_imm8_effect_step 0x1093f0 0x49 0xc6 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1093f4 [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x1093f4) (movR64R64Effect 0x1093f4 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1093f4 6 7).toInstrSpec (mov_r64_r64_effect_step 0x1093f4 0x48 0xfe (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (9, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093a8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (8, 55), (9, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093ad) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (8, 55), (9, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093b2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 4), (5, 5), (8, 55), (9, 53), (10, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093b5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 57), (4, 4), (5, 5), (8, 55), (9, 53), (10, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093b9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (2, 57), (4, 4), (5, 5), (8, 55), (9, 53), (10, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093be) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 63), (2, 57), (4, 4), (5, 5), (8, 55), (9, 53), (10, 61), (13, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093c1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 63), (2, 57), (4, 4), (5, 5), (8, 55), (9, 53), (10, 61), (13, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093c5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 63), (1, 69), (2, 57), (4, 4), (5, 5), (8, 55), (9, 53), (10, 61), (13, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093ca) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 63), (1, 69), (2, 57), (4, 4), (5, 5), (6, 71), (8, 55), (9, 53), (10, 61), (13, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093cd) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 63), (1, 69), (2, 57), (4, 4), (5, 5), (6, 73), (8, 55), (9, 53), (10, 61), (13, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093d1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 63), (1, 69), (2, 57), (4, 4), (5, 5), (6, 73), (8, 55), (9, 53), (10, 61), (11, 75), (13, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093d4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 63), (1, 69), (2, 57), (4, 4), (5, 5), (6, 73), (8, 55), (9, 53), (10, 61), (11, 75), (13, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093dc) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 63), (1, 69), (2, 57), (4, 4), (5, 5), (6, 73), (7, 78), (8, 55), (9, 53), (10, 61), (11, 75), (13, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093e1) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 63), (1, 69), (2, 57), (4, 4), (5, 5), (6, 73), (7, 78), (8, 55), (9, 53), (10, 61), (11, 75), (13, 67), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093e4) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 63), (1, 69), (2, 57), (4, 4), (5, 5), (6, 73), (7, 78), (8, 55), (9, 53), (10, 61), (11, 75), (13, 67), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093e8) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 63), (1, 69), (2, 57), (3, 84), (4, 4), (5, 5), (6, 73), (7, 78), (8, 55), (9, 53), (10, 61), (11, 75), (13, 67), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093ed) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 63), (1, 69), (2, 57), (3, 84), (4, 4), (5, 5), (6, 73), (7, 78), (8, 55), (9, 53), (10, 61), (11, 75), (13, 67), (14, 86), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093f0) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 63), (1, 69), (2, 57), (3, 84), (4, 4), (5, 5), (6, 73), (7, 78), (8, 55), (9, 53), (10, 61), (11, 75), (13, 67), (14, 88), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093f4) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 63), (1, 69), (2, 57), (3, 84), (4, 4), (5, 5), (6, 90), (7, 78), (8, 55), (9, 53), (10, 61), (11, 75), (13, 67), (14, 88), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093f7) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1093a3_1 code

theorem block_l1093a3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1093a3 :=
  Rest.liftedBlock (rest_l1093a3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1093a3 x hx)

theorem rest_l109509 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109509 bytes_l109509) (entryMap (live .l109509))
      12 0x109509 bytes_l109509 b_l109509 := by
  have f0 : InstrSpec 0x109509 [0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00] (StorePre 0x109509 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x109509 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x109509 (.sib 4 none 0 (.d8 0x40)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x109509 (.sib 4 none 0 (.d8 0x40)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x109509 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x109512 [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x109512 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109512 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x109512 (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x109512 (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x109512 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10951b [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10951b 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10951b + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10951b (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10951b (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10951b 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x109524 [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x109524 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109524 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x109524 (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x109524 (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x109524 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10952d [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10952d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10952d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10952d (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10952d (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10952d 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x109536 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x109536 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109536 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x109536 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x109536 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x109536 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10953f [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10953f 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10953f + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10953f (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10953f (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10953f 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x109548 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x109548 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109548 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x109548 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x109548 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x109548 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x109551 [0x4C, 0x8B, 0xA4, 0x24, 0xE8, 0x00, 0x00, 0x00] (LoadPre 0x109551 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x109551 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109551 12 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x109551 12 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_r64_m64_effect_step 0x109551 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x109559 [0x4D, 0x85, 0xE4] (fun s => s.RIP = 0x109559) (testR64R64Effect 0x109559 12 12)
      [.gpr 12, .gpr 12] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x109559 12 12).toInstrSpec (test_r64_r64_effect_step 0x109559 0x4d 0xe4 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10955c [0x48, 0x8B, 0xAC, 0x24, 0xF0, 0x00, 0x00, 0x00] (LoadPre 0x10955c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10955c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10955c 5 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x10955c 5 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x10955c 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109512) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10951b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109524) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10952d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109536) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10953f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109548) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109551) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 61), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109559) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f9 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 61), (13, 13), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10955c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 61), (13, 13), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109564) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 67) (jcc_rel32_effect_step 0x109564 4 0x3f7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l109509 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109509 :=
  Rest.liftedBlock (rest_l109509 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109509 x hx)

theorem rest_l10956a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10956a bytes_l10956a) (entryMap (live .l10956a))
      12 0x10956a bytes_l10956a b_l10956a := by
  have f0 : InstrSpec 0x10956a [0x48, 0xB8, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F] (fun s => s.RIP = 0x10956a) (movR64Imm64Effect 0x10956a 0 0xffffffffffffffc)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x10956a 0 0xffffffffffffffc).toInstrSpec (mov_r64_imm64_effect_step 0x10956a 0x48 0xb8 (by decide) (by decide) 0xffffffffffffffc) pre_rip
  have f1 : InstrSpec 0x109574 [0x48, 0x8B, 0x8C, 0x24, 0x40, 0x01, 0x00, 0x00] (LoadPre 0x109574 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x109574 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109574 1 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109574 1 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_r64_m64_effect_step 0x109574 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10957c [0x48, 0x21, 0xC1] (fun s => s.RIP = 0x10957c) (andR64R64Effect 0x10957c 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10957c 1 0).toInstrSpec (and_r64_r64_effect_step 0x10957c 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10957f [0x48, 0xC1, 0xE1, 0x04] (fun s => s.RIP = 0x10957f) (shlR64Effect 0x10957f 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x10957f 4 1 4).toInstrSpec (shl_r64_imm8_effect_step 0x10957f 0x48 0xe1 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x109583 [0x48, 0x01, 0xCD] (fun s => s.RIP = 0x109583) (addR64R64Effect 0x109583 5 1)
      [.gpr 5, .gpr 1] [] [.reg 5, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109583 5 1).toInstrSpec (add_r64_r64_effect_step 0x109583 0x48 0xcd (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x109586 [0x48, 0x01, 0xCA] (fun s => s.RIP = 0x109586) (addR64R64Effect 0x109586 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109586 2 1).toInstrSpec (add_r64_r64_effect_step 0x109586 0x48 0xca (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x109589 [0x48, 0x89, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x109589 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x109589 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109589 2 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109589 2 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x109589 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x109591 [0x41, 0xC1, 0xE4, 0x04] (fun s => s.RIP = 0x109591) (shlR32Effect 0x109591 4 12 4)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shlR32Effect_footprint 0x109591 4 12 4).toInstrSpec (shl_r32_imm8_rex_effect_step 0x109591 0x41 0xe4 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x109595 [0x48, 0x8B, 0x9C, 0x24, 0x50, 0x01, 0x00, 0x00] (LoadPre 0x109595 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x109595 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109595 3 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x109595 3 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (mov_r64_m64_effect_step 0x109595 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10959d [0x45, 0x31, 0xED] (fun s => s.RIP = 0x10959d) (xorR32R32Effect 0x10959d 3 13 13)
      [.gpr 13, .gpr 13] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10959d 3 13 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x10959d 0x45 0xed (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1095a0 [0x4C, 0x8D, 0xB4, 0x24, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1095a0) (leaR64Effect 0x1095a0 14 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x1095a0 14 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (lea_r64_effect_step 0x1095a0 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1095a8 [0x4C, 0x8D, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1095a8) (leaR64Effect 0x1095a8 15 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x1095a8 15 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x1095a8 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109574) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10957c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (2, 2), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10957f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 59), (2, 2), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109583) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 59), (2, 2), (4, 4), (5, 61), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109586) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 59), (2, 63), (4, 4), (5, 61), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109589) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 59), (2, 63), (4, 4), (5, 61), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109591) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 59), (2, 63), (4, 4), (5, 61), (9, 9), (12, 66), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109595) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 59), (2, 63), (3, 68), (4, 4), (5, 61), (9, 9), (12, 66), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10959d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 59), (2, 63), (3, 68), (4, 4), (5, 61), (9, 9), (12, 66), (13, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095a0) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 59), (2, 63), (3, 68), (4, 4), (5, 61), (9, 9), (12, 66), (13, 70), (14, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095a8) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 59), (2, 63), (3, 68), (4, 4), (5, 61), (9, 9), (12, 66), (13, 70), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095b0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 76) (by decide) rfl

theorem block_l10956a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10956a :=
  Rest.liftedBlock (rest_l10956a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10956a x hx)

theorem rest_l1095b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1095b0 bytes_l1095b0) (entryMap (live .l1095b0))
      15 0x1095b0 bytes_l1095b0 b_l1095b0 := by
  have f0 : InstrSpec 0x1095b0 [0x41, 0x8B, 0x41, 0x10] (LoadPre 0x1095b0 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x1095b0 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1095b0 0 (.base 9 (.d8 0x10)))
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR32M32Effect_footprint 0x1095b0 0 (.base 9 (.d8 0x10))).toInstrSpec (mov_r32_m32_effect_step 0x1095b0 0x41 (by decide) 0 (.base 9 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1095b4 [0x49, 0x8B, 0x09] (LoadPre 0x1095b4 (fun s => AddrMode.addr (.base 9 .none) s (0x1095b4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1095b4 1 (.base 9 .none))
      [.gpr 9] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1095b4 1 (.base 9 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1095b4 0x49 (by decide) 1 (.base 9 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1095b7 [0x41, 0x8B, 0x51, 0x08] (LoadPre 0x1095b7 (fun s => AddrMode.addr (.base 9 (.d8 0x8)) s (0x1095b7 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1095b7 2 (.base 9 (.d8 0x8)))
      [.gpr 9] [] [.reg 2, .rip] :=
    (movR32M32Effect_footprint 0x1095b7 2 (.base 9 (.d8 0x8))).toInstrSpec (mov_r32_m32_effect_step 0x1095b7 0x41 (by decide) 2 (.base 9 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1095bb [0x41, 0x8B, 0x71, 0x0C] (LoadPre 0x1095bb (fun s => AddrMode.addr (.base 9 (.d8 0xc)) s (0x1095bb + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1095bb 6 (.base 9 (.d8 0xc)))
      [.gpr 9] [] [.reg 6, .rip] :=
    (movR32M32Effect_footprint 0x1095bb 6 (.base 9 (.d8 0xc))).toInstrSpec (mov_r32_m32_effect_step 0x1095bb 0x41 (by decide) 6 (.base 9 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1095bf [0x01, 0xC6] (fun s => s.RIP = 0x1095bf) (addR32R32Effect 0x1095bf 2 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1095bf 2 6 0).toInstrSpec (add_r32_r32_effect_step 0x1095bf 0xc6 (by decide)) pre_rip
  have f5 : InstrSpec 0x1095c1 [0x0F, 0xCE] (fun s => s.RIP = 0x1095c1) (bswapR32Effect 0x1095c1 2 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (bswapR32Effect_footprint 0x1095c1 2 6).toInstrSpec (bswap_r32_effect_step 0x1095c1 0xce (by decide)) pre_rip
  have f6 : InstrSpec 0x1095c3 [0xFF, 0xC0] (fun s => s.RIP = 0x1095c3) (incR32Effect 0x1095c3 2 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (incR32Effect_footprint 0x1095c3 2 0).toInstrSpec (inc_r32_effect_step 0x1095c3 0xc0 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1095c5 [0x41, 0x89, 0x41, 0x10] (StorePre 0x1095c5 4 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x1095c5 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1095c5 0 (.base 9 (.d8 0x10)))
      [.gpr 0, .gpr 9] [] [.rip] :=
    (movM32R32Effect_footprint 0x1095c5 0 (.base 9 (.d8 0x10))).toInstrSpec (mov_m32_r32_effect_step 0x1095c5 0x41 (by decide) 0 (.base 9 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1095c9 [0x48, 0x89, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x1095c9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x1095c9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1095c9 1 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1095c9 1 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m64_r64_effect_step 0x1095c9 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1095d1 [0x89, 0x94, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x1095d1 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1095d1 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1095d1 2 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1095d1 2 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m32_r32_low_effect_step 0x1095d1 2 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1095d8 [0x89, 0xB4, 0x24, 0x0C, 0x01, 0x00, 0x00] (StorePre 0x1095d8 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10c)) s (0x1095d8 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1095d8 6 (.sib 4 none 0 (.d32 0x10c)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1095d8 6 (.sib 4 none 0 (.d32 0x10c))).toInstrSpec (mov_m32_r32_low_effect_step 0x1095d8 6 (.sib 4 none 0 (.d32 0x10c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1095df [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x1095df) (movR64R64Effect 0x1095df 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1095df 7 14).toInstrSpec (mov_r64_r64_effect_step 0x1095df 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1095e2 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x1095e2) (movR64R64Effect 0x1095e2 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1095e2 6 3).toInstrSpec (mov_r64_r64_effect_step 0x1095e2 0x48 0xde (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1095e5 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x1095e5) (movR64R64Effect 0x1095e5 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1095e5 2 15).toInstrSpec (mov_r64_r64_effect_step 0x1095e5 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1095e8 [0xE8, 0x73, 0xD3, 0xFF, 0xFF] (PushPre 0x1095e8 5) (callEffect (fun _ => 0x106960) 0x1095ed)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1095e8 0x106960 0x1095ed).toInstrSpec (call_rel32_effect_step 0x1095e8 0xffffd373 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095b4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095b7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095bb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095bf) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 61), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095c1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095c3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095c5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095c9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 65), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095d1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 65), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095d8) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095df) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 65), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 71), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095e2) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 65), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095e5) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 65), (1, 55), (2, 75), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095e8) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 65), (1, 55), (2, 75), (3, 3), (4, 77), (5, 5), (6, 73), (7, 71), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106960) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 79) (by decide) (by decide) rfl rfl

theorem block_l1095b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1095b0 :=
  Rest.liftedBlock (rest_l1095b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1095b0 x hx)

theorem rest_l1095ed [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1095ed bytes_l1095ed) (entryMap (live .l1095ed))
      8 0x1095ed bytes_l1095ed b_l1095ed := by
  have f0 : InstrSpec 0x1095ed [0x4C, 0x8B, 0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00] (LoadPre 0x1095ed (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x1095ed + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1095ed 9 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1095ed 9 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_r64_m64_effect_step 0x1095ed 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1095f5 [0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x1095f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1095f5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1095f5 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1095f5 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x1095f5 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1095fd [0x48, 0x8B, 0x8C, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x1095fd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1095fd + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1095fd 1 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1095fd 1 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x1095fd 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x109605 [0x4A, 0x89, 0x4C, 0x2C, 0x10] (StorePre 0x109605 5 (fun s => AddrMode.addr (.sib 4 (some 13) 0 (.d8 0x10)) s (0x109605 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109605 1 (.sib 4 (some 13) 0 (.d8 0x10)))
      [.gpr 1, .gpr 4, .gpr 13] [] [.rip] :=
    (movM64R64Effect_footprint 0x109605 1 (.sib 4 (some 13) 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x109605 0x4a (by decide) 1 (.sib 4 (some 13) 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10960a [0x4A, 0x89, 0x44, 0x2C, 0x08] (StorePre 0x10960a 5 (fun s => AddrMode.addr (.sib 4 (some 13) 0 (.d8 0x8)) s (0x10960a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10960a 0 (.sib 4 (some 13) 0 (.d8 0x8)))
      [.gpr 0, .gpr 4, .gpr 13] [] [.rip] :=
    (movM64R64Effect_footprint 0x10960a 0 (.sib 4 (some 13) 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10960a 0x4a (by decide) 0 (.sib 4 (some 13) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10960f [0x49, 0x83, 0xC5, 0x10] (fun s => s.RIP = 0x10960f) (addR64Imm8Effect 0x10960f 13 0x10)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10960f 13 0x10).toInstrSpec (add_r64_imm8_effect_step 0x10960f 0x49 0xc5 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x109613 [0x4D, 0x39, 0xEC] (fun s => s.RIP = 0x109613) (cmpR64R64Effect 0x109613 12 13)
      [.gpr 12, .gpr 13] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x109613 12 13).toInstrSpec (cmp_r64_r64_effect_step 0x109613 0x4d 0xec (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095f5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095fd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109605) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10960a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10960f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109613) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 61), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109616) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 65) (jcc_rel8_effect_step 0x109616 5 0x98) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1095ed [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1095ed :=
  Rest.liftedBlock (rest_l1095ed code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1095ed x hx)

theorem rest_l109618_3 [Bindings] (code : CodeMap) :
    Rest (n := 153) code lifted (codeRange 0x109618 bytes_l109618) [(0, 149), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (19, 151), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x109733 bytes_l109618_3 b_l109618_3 := by
  exact Rest.jcc (n := 153) (jcc_rel32_effect_step 0x109733 4 0x228) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l109618_2 [Bindings] (code : CodeMap) :
    Rest (n := 128) code lifted (codeRange 0x109618 bytes_l109618) [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 125), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]
      21 0x1096d9 bytes_l109618_2 b_l109618_2 := by
  have f40 : InstrSpec 0x1096d9 [0x0F, 0xB6, 0x74, 0x24, 0x78] (LoadPre 0x1096d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1096d9 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1096d9 5 6 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x1096d9 5 6 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (movzx_r32_m8_effect_step 0x1096d9 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x1096de [0x40, 0x88, 0x70, 0x01] (StorePre 0x1096de 4 (fun s => AddrMode.addr (.base 0 (.d8 0x1)) s (0x1096de + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1096de 4 6 (.base 0 (.d8 0x1)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x1096de 4 6 (.base 0 (.d8 0x1))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1096de 0x40 (by decide) 6 (.base 0 (.d8 0x1)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x1096e2 [0x0F, 0xB6, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x1096e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1096e2 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1096e2 8 6 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x1096e2 8 6 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (movzx_r32_m8_effect_step 0x1096e2 6 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f43 : InstrSpec 0x1096ea [0x40, 0x88, 0x70, 0x02] (StorePre 0x1096ea 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2)) s (0x1096ea + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1096ea 4 6 (.base 0 (.d8 0x2)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x1096ea 4 6 (.base 0 (.d8 0x2))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1096ea 0x40 (by decide) 6 (.base 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f44 : InstrSpec 0x1096ee [0x0F, 0xB6, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x1096ee (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1096ee + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1096ee 8 6 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x1096ee 8 6 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (movzx_r32_m8_effect_step 0x1096ee 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f45 : InstrSpec 0x1096f6 [0x40, 0x88, 0x70, 0x03] (StorePre 0x1096f6 4 (fun s => AddrMode.addr (.base 0 (.d8 0x3)) s (0x1096f6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1096f6 4 6 (.base 0 (.d8 0x3)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x1096f6 4 6 (.base 0 (.d8 0x3))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1096f6 0x40 (by decide) 6 (.base 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f46 : InstrSpec 0x1096fa [0x40, 0x88, 0x78, 0x04] (StorePre 0x1096fa 4 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x1096fa + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1096fa 4 7 (.base 0 (.d8 0x4)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x1096fa 4 7 (.base 0 (.d8 0x4))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1096fa 0x40 (by decide) 7 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f47 : InstrSpec 0x1096fe [0x44, 0x88, 0x40, 0x05] (StorePre 0x1096fe 4 (fun s => AddrMode.addr (.base 0 (.d8 0x5)) s (0x1096fe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1096fe 4 8 (.base 0 (.d8 0x5)))
      [.gpr 8, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x1096fe 4 8 (.base 0 (.d8 0x5))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1096fe 0x44 (by decide) 0 (.base 0 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x109702 [0x44, 0x88, 0x48, 0x06] (StorePre 0x109702 4 (fun s => AddrMode.addr (.base 0 (.d8 0x6)) s (0x109702 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109702 4 9 (.base 0 (.d8 0x6)))
      [.gpr 9, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x109702 4 9 (.base 0 (.d8 0x6))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109702 0x44 (by decide) 1 (.base 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x109706 [0x44, 0x88, 0x50, 0x07] (StorePre 0x109706 4 (fun s => AddrMode.addr (.base 0 (.d8 0x7)) s (0x109706 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109706 4 10 (.base 0 (.d8 0x7)))
      [.gpr 10, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x109706 4 10 (.base 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109706 0x44 (by decide) 2 (.base 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f50 : InstrSpec 0x10970a [0x44, 0x88, 0x58, 0x08] (StorePre 0x10970a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x10970a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10970a 4 11 (.base 0 (.d8 0x8)))
      [.gpr 11, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10970a 4 11 (.base 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10970a 0x44 (by decide) 3 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f51 : InstrSpec 0x10970e [0x88, 0x58, 0x09] (StorePre 0x10970e 3 (fun s => AddrMode.addr (.base 0 (.d8 0x9)) s (0x10970e + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10970e 3 3 (.base 0 (.d8 0x9)))
      [.gpr 3, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10970e 3 3 (.base 0 (.d8 0x9))).toInstrSpec (mov_m8_r8_effect_step 0x10970e 3 (by decide) (.base 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x109711 [0x40, 0x88, 0x68, 0x0A] (StorePre 0x109711 4 (fun s => AddrMode.addr (.base 0 (.d8 0xa)) s (0x109711 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109711 4 5 (.base 0 (.d8 0xa)))
      [.gpr 5, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x109711 4 5 (.base 0 (.d8 0xa))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109711 0x40 (by decide) 5 (.base 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f53 : InstrSpec 0x109715 [0x44, 0x88, 0x70, 0x0B] (StorePre 0x109715 4 (fun s => AddrMode.addr (.base 0 (.d8 0xb)) s (0x109715 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109715 4 14 (.base 0 (.d8 0xb)))
      [.gpr 14, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x109715 4 14 (.base 0 (.d8 0xb))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109715 0x44 (by decide) 6 (.base 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x109719 [0x44, 0x88, 0x78, 0x0C] (StorePre 0x109719 4 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x109719 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109719 4 15 (.base 0 (.d8 0xc)))
      [.gpr 15, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x109719 4 15 (.base 0 (.d8 0xc))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109719 0x44 (by decide) 7 (.base 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f55 : InstrSpec 0x10971d [0x44, 0x88, 0x60, 0x0D] (StorePre 0x10971d 4 (fun s => AddrMode.addr (.base 0 (.d8 0xd)) s (0x10971d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10971d 4 12 (.base 0 (.d8 0xd)))
      [.gpr 12, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10971d 4 12 (.base 0 (.d8 0xd))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10971d 0x44 (by decide) 4 (.base 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x109721 [0x44, 0x88, 0x68, 0x0E] (StorePre 0x109721 4 (fun s => AddrMode.addr (.base 0 (.d8 0xe)) s (0x109721 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109721 4 13 (.base 0 (.d8 0xe)))
      [.gpr 13, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x109721 4 13 (.base 0 (.d8 0xe))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109721 0x44 (by decide) 5 (.base 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f57 : InstrSpec 0x109725 [0x88, 0x48, 0x0F] (StorePre 0x109725 3 (fun s => AddrMode.addr (.base 0 (.d8 0xf)) s (0x109725 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109725 3 1 (.base 0 (.d8 0xf)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x109725 3 1 (.base 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_effect_step 0x109725 1 (by decide) (.base 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f58 : InstrSpec 0x109728 [0x48, 0x8B, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00] (LoadPre 0x109728 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x109728 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109728 0 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109728 0 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_r64_m64_effect_step 0x109728 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f59 : InstrSpec 0x109730 [0x83, 0xF8, 0x01] (fun s => s.RIP = 0x109730) (cmpR32Imm8Effect 0x109730 3 0 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x109730 3 0 0x1).toInstrSpec (cmp_r32_imm8_effect_step 0x109730 0xf8 0x1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f40 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 128), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096de) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.exec (n := 130) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 128), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096e2) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f42 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 131), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096ea) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.exec (n := 133) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 131), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096ee) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f44 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096f6) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.exec (n := 136) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096fa) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 137) (RestInside.exec (n := 137) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096fe) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 138) (RestInside.exec (n := 138) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109702) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 139) (RestInside.exec (n := 139) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109706) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 140) (RestInside.exec (n := 140) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10970a) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 141) (RestInside.exec (n := 141) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10970e) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 142) (RestInside.exec (n := 142) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109711) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 143) (RestInside.exec (n := 143) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109715) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 144) (RestInside.exec (n := 144) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109719) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 145) (RestInside.exec (n := 145) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10971d) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 146) (RestInside.exec (n := 146) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109721) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 147) (RestInside.exec (n := 147) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109725) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 148) (RestInside.exec (n := 148) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109728) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f58 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 149), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109730) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f59 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 149), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (19, 151), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109733) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109618_3 code

theorem rest_l109618_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x109618 bytes_l109618) [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (10, 87), (22, 22), (39, 39), (50, 50), (51, 51)]
      41 0x109678 bytes_l109618_1 b_l109618_1 := by
  have f20 : InstrSpec 0x109678 [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x10] (LoadPre 0x109678 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109678 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109678 6 11 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x109678 6 11 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x109678 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x10967e [0x44, 0x32, 0x5D, 0x08] (LoadPre 0x10967e (fun s => AddrMode.addr (.base 5 (.d8 0x8)) s (0x10967e + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10967e 4 11 (.base 5 (.d8 0x8)))
      [.gpr 11, .gpr 5] [] [.reg 11, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10967e 4 11 (.base 5 (.d8 0x8))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10967e 0x44 (by decide) 3 (.base 5 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x109682 [0x0F, 0xB6, 0x5C, 0x24, 0x11] (LoadPre 0x109682 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x109682 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109682 5 3 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x109682 5 3 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (movzx_r32_m8_effect_step 0x109682 3 (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x109687 [0x32, 0x5D, 0x09] (LoadPre 0x109687 (fun s => AddrMode.addr (.base 5 (.d8 0x9)) s (0x109687 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x109687 3 3 (.base 5 (.d8 0x9)))
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x109687 3 3 (.base 5 (.d8 0x9))).toInstrSpec (xor_r8_m8_effect_step 0x109687 3 (by decide) (.base 5 (.d8 0x9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x10968a [0x48, 0x89, 0xEA] (fun s => s.RIP = 0x10968a) (movR64R64Effect 0x10968a 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10968a 2 5).toInstrSpec (mov_r64_r64_effect_step 0x10968a 0x48 0xea (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x10968d [0x0F, 0xB6, 0x6C, 0x24, 0x12] (LoadPre 0x10968d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x10968d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10968d 5 5 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x10968d 5 5 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (movzx_r32_m8_effect_step 0x10968d 5 (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x109692 [0x40, 0x32, 0x6A, 0x0A] (LoadPre 0x109692 (fun s => AddrMode.addr (.base 2 (.d8 0xa)) s (0x109692 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109692 4 5 (.base 2 (.d8 0xa)))
      [.gpr 5, .gpr 2] [] [.reg 5, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x109692 4 5 (.base 2 (.d8 0xa))).toInstrSpec (xor_r8_m8_rex_effect_step 0x109692 0x40 (by decide) 5 (.base 2 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x109696 [0x44, 0x0F, 0xB6, 0x74, 0x24, 0x13] (LoadPre 0x109696 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x109696 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109696 6 14 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x109696 6 14 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x109696 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x10969c [0x44, 0x32, 0x72, 0x0B] (LoadPre 0x10969c (fun s => AddrMode.addr (.base 2 (.d8 0xb)) s (0x10969c + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10969c 4 14 (.base 2 (.d8 0xb)))
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10969c 4 14 (.base 2 (.d8 0xb))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10969c 0x44 (by decide) 6 (.base 2 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x1096a0 [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x14] (LoadPre 0x1096a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1096a0 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1096a0 6 15 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x1096a0 6 15 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1096a0 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x1096a6 [0x44, 0x32, 0x7A, 0x0C] (LoadPre 0x1096a6 (fun s => AddrMode.addr (.base 2 (.d8 0xc)) s (0x1096a6 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1096a6 4 15 (.base 2 (.d8 0xc)))
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1096a6 4 15 (.base 2 (.d8 0xc))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1096a6 0x44 (by decide) 7 (.base 2 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x1096aa [0x44, 0x0F, 0xB6, 0x64, 0x24, 0x15] (LoadPre 0x1096aa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x1096aa + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1096aa 6 12 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x1096aa 6 12 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1096aa 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x1096b0 [0x44, 0x32, 0x62, 0x0D] (LoadPre 0x1096b0 (fun s => AddrMode.addr (.base 2 (.d8 0xd)) s (0x1096b0 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1096b0 4 12 (.base 2 (.d8 0xd)))
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1096b0 4 12 (.base 2 (.d8 0xd))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1096b0 0x44 (by decide) 4 (.base 2 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x1096b4 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x16] (LoadPre 0x1096b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x1096b4 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1096b4 6 13 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1096b4 6 13 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1096b4 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f34 : InstrSpec 0x1096ba [0x44, 0x32, 0x6A, 0x0E] (LoadPre 0x1096ba (fun s => AddrMode.addr (.base 2 (.d8 0xe)) s (0x1096ba + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1096ba 4 13 (.base 2 (.d8 0xe)))
      [.gpr 13, .gpr 2] [] [.reg 13, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1096ba 4 13 (.base 2 (.d8 0xe))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1096ba 0x44 (by decide) 5 (.base 2 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x1096be [0x0F, 0xB6, 0x4C, 0x24, 0x17] (LoadPre 0x1096be (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x1096be + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1096be 5 1 (.sib 4 none 0 (.d8 0x17)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1096be 5 1 (.sib 4 none 0 (.d8 0x17))).toInstrSpec (movzx_r32_m8_effect_step 0x1096be 1 (.sib 4 none 0 (.d8 0x17)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x1096c3 [0x32, 0x4A, 0x0F] (LoadPre 0x1096c3 (fun s => AddrMode.addr (.base 2 (.d8 0xf)) s (0x1096c3 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1096c3 3 1 (.base 2 (.d8 0xf)))
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1096c3 3 1 (.base 2 (.d8 0xf))).toInstrSpec (xor_r8_m8_effect_step 0x1096c3 1 (by decide) (.base 2 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x1096c6 [0x48, 0x8B, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x1096c6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1096c6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1096c6 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1096c6 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x1096c6 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f38 : InstrSpec 0x1096ce [0x0F, 0xB6, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x1096ce (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1096ce + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1096ce 8 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x1096ce 8 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (movzx_r32_m8_effect_step 0x1096ce 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x1096d6 [0x40, 0x88, 0x30] (StorePre 0x1096d6 3 (fun s => AddrMode.addr (.base 0 .none) s (0x1096d6 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1096d6 3 6 (.base 0 .none))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x1096d6 3 6 (.base 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x1096d6 0x40 (by decide) 6 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f20 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (10, 87), (11, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10967e) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f21 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109682) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f22 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 70), (1, 60), (3, 93), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109687) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f23 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 70), (1, 60), (3, 95), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10968a) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f24 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10968d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f25 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 99), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109692) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f26 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109696) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f27 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (14, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10969c) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f28 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (14, 105), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096a0) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f29 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (14, 105), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096a6) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f30 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096aa) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f31 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096b0) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f32 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096b4) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f33 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 115), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096ba) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f34 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096be) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f35 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 70), (1, 119), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096c3) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 70), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096c6) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096ce) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f38 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 125), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096d6) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.exec (n := 127) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 125), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096d9) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l109618_2 code

theorem rest_l109618 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109618 bytes_l109618) (entryMap (live .l109618))
      61 0x109618 bytes_l109618 b_l109618 := by
  have f0 : InstrSpec 0x109618 [0x0F, 0xB6, 0x44, 0x24, 0x08] (LoadPre 0x109618 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109618 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109618 5 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109618 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x109618 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10961d [0x0F, 0xB6, 0x4C, 0x24, 0x09] (LoadPre 0x10961d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x10961d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10961d 5 1 (.sib 4 none 0 (.d8 0x9)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10961d 5 1 (.sib 4 none 0 (.d8 0x9))).toInstrSpec (movzx_r32_m8_effect_step 0x10961d 1 (.sib 4 none 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x109622 [0x32, 0x45, 0x00] (LoadPre 0x109622 (fun s => AddrMode.addr (.base 5 (.d8 0x0)) s (0x109622 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x109622 3 0 (.base 5 (.d8 0x0)))
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x109622 3 0 (.base 5 (.d8 0x0))).toInstrSpec (xor_r8_m8_effect_step 0x109622 0 (by decide) (.base 5 (.d8 0x0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x109625 [0x88, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x109625 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109625 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x109625 7 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109625 7 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m8_r8_effect_step 0x109625 0 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10962c [0x32, 0x4D, 0x01] (LoadPre 0x10962c (fun s => AddrMode.addr (.base 5 (.d8 0x1)) s (0x10962c + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10962c 3 1 (.base 5 (.d8 0x1)))
      [.gpr 1, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10962c 3 1 (.base 5 (.d8 0x1))).toInstrSpec (xor_r8_m8_effect_step 0x10962c 1 (by decide) (.base 5 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10962f [0x88, 0x4C, 0x24, 0x78] (StorePre 0x10962f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10962f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10962f 4 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10962f 4 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m8_r8_effect_step 0x10962f 1 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x109633 [0x0F, 0xB6, 0x44, 0x24, 0x0A] (LoadPre 0x109633 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x109633 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109633 5 0 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109633 5 0 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (movzx_r32_m8_effect_step 0x109633 0 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x109638 [0x32, 0x45, 0x02] (LoadPre 0x109638 (fun s => AddrMode.addr (.base 5 (.d8 0x2)) s (0x109638 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x109638 3 0 (.base 5 (.d8 0x2)))
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x109638 3 0 (.base 5 (.d8 0x2))).toInstrSpec (xor_r8_m8_effect_step 0x109638 0 (by decide) (.base 5 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10963b [0x88, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x10963b 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10963b + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10963b 7 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10963b 7 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m8_r8_effect_step 0x10963b 0 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x109642 [0x0F, 0xB6, 0x44, 0x24, 0x0B] (LoadPre 0x109642 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x109642 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109642 5 0 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109642 5 0 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (movzx_r32_m8_effect_step 0x109642 0 (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x109647 [0x32, 0x45, 0x03] (LoadPre 0x109647 (fun s => AddrMode.addr (.base 5 (.d8 0x3)) s (0x109647 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x109647 3 0 (.base 5 (.d8 0x3)))
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x109647 3 0 (.base 5 (.d8 0x3))).toInstrSpec (xor_r8_m8_effect_step 0x109647 0 (by decide) (.base 5 (.d8 0x3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10964a [0x88, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x10964a 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10964a + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10964a 7 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10964a 7 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m8_r8_effect_step 0x10964a 0 (by decide) (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x109651 [0x0F, 0xB6, 0x7C, 0x24, 0x0C] (LoadPre 0x109651 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x109651 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109651 5 7 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x109651 5 7 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x109651 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x109656 [0x40, 0x32, 0x7D, 0x04] (LoadPre 0x109656 (fun s => AddrMode.addr (.base 5 (.d8 0x4)) s (0x109656 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109656 4 7 (.base 5 (.d8 0x4)))
      [.gpr 7, .gpr 5] [] [.reg 7, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x109656 4 7 (.base 5 (.d8 0x4))).toInstrSpec (xor_r8_m8_rex_effect_step 0x109656 0x40 (by decide) 7 (.base 5 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10965a [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x0D] (LoadPre 0x10965a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x10965a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10965a 6 8 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x10965a 6 8 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10965a 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x109660 [0x44, 0x32, 0x45, 0x05] (LoadPre 0x109660 (fun s => AddrMode.addr (.base 5 (.d8 0x5)) s (0x109660 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109660 4 8 (.base 5 (.d8 0x5)))
      [.gpr 8, .gpr 5] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x109660 4 8 (.base 5 (.d8 0x5))).toInstrSpec (xor_r8_m8_rex_effect_step 0x109660 0x44 (by decide) 0 (.base 5 (.d8 0x5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x109664 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x0E] (LoadPre 0x109664 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x109664 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109664 6 9 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x109664 6 9 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x109664 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10966a [0x44, 0x32, 0x4D, 0x06] (LoadPre 0x10966a (fun s => AddrMode.addr (.base 5 (.d8 0x6)) s (0x10966a + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10966a 4 9 (.base 5 (.d8 0x6)))
      [.gpr 9, .gpr 5] [] [.reg 9, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10966a 4 9 (.base 5 (.d8 0x6))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10966a 0x44 (by decide) 1 (.base 5 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x10966e [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x0F] (LoadPre 0x10966e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x10966e + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10966e 6 10 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x10966e 6 10 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10966e 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x109674 [0x44, 0x32, 0x55, 0x07] (LoadPre 0x109674 (fun s => AddrMode.addr (.base 5 (.d8 0x7)) s (0x109674 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109674 4 10 (.base 5 (.d8 0x7)))
      [.gpr 10, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x109674 4 10 (.base 5 (.d8 0x7))).toInstrSpec (xor_r8_m8_rex_effect_step 0x109674 0x44 (by decide) 2 (.base 5 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10961d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109622) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109625) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 57), (1, 55), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10962c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 57), (1, 60), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10962f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 60), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109633) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 60), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109638) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 60), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10963b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (1, 60), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109642) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 60), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109647) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10964a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109651) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109656) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10965a) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109660) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109664) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 79), (9, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10966a) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10966e) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (10, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109674) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (10, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109678) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109618_1 code

theorem block_l109618 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109618 :=
  Rest.liftedBlock (rest_l109618 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109618 x hx)

theorem rest_l109739_3 [Bindings] (code : CodeMap) :
    Rest (n := 153) code lifted (codeRange 0x109739 bytes_l109739) [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (19, 151), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x109861 bytes_l109739_3 b_l109739_3 := by
  exact Rest.jcc (n := 153) (jcc_rel32_effect_step 0x109861 4 0xfa) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l109739_2 [Bindings] (code : CodeMap) :
    Rest (n := 128) code lifted (codeRange 0x109739 bytes_l109739) [(0, 119), (1, 126), (2, 2), (3, 95), (4, 4), (5, 99), (6, 123), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]
      21 0x109802 bytes_l109739_2 b_l109739_2 := by
  have f40 : InstrSpec 0x109802 [0x0F, 0xB6, 0x74, 0x24, 0x78] (LoadPre 0x109802 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109802 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109802 5 6 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x109802 5 6 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (movzx_r32_m8_effect_step 0x109802 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x109807 [0x40, 0x88, 0x71, 0x11] (StorePre 0x109807 4 (fun s => AddrMode.addr (.base 1 (.d8 0x11)) s (0x109807 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109807 4 6 (.base 1 (.d8 0x11)))
      [.gpr 6, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x109807 4 6 (.base 1 (.d8 0x11))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109807 0x40 (by decide) 6 (.base 1 (.d8 0x11)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x10980b [0x48, 0x8B, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x10980b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10980b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10980b 1 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10980b 1 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x10980b 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f43 : InstrSpec 0x109813 [0x0F, 0xB6, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x109813 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x109813 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x109813 8 6 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x109813 8 6 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (movzx_r32_m8_effect_step 0x109813 6 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f44 : InstrSpec 0x10981b [0x40, 0x88, 0x71, 0x12] (StorePre 0x10981b 4 (fun s => AddrMode.addr (.base 1 (.d8 0x12)) s (0x10981b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10981b 4 6 (.base 1 (.d8 0x12)))
      [.gpr 6, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x10981b 4 6 (.base 1 (.d8 0x12))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10981b 0x40 (by decide) 6 (.base 1 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x10981f [0x0F, 0xB6, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x10981f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10981f + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10981f 8 6 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x10981f 8 6 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (movzx_r32_m8_effect_step 0x10981f 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f46 : InstrSpec 0x109827 [0x40, 0x88, 0x71, 0x13] (StorePre 0x109827 4 (fun s => AddrMode.addr (.base 1 (.d8 0x13)) s (0x109827 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109827 4 6 (.base 1 (.d8 0x13)))
      [.gpr 6, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x109827 4 6 (.base 1 (.d8 0x13))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109827 0x40 (by decide) 6 (.base 1 (.d8 0x13)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f47 : InstrSpec 0x10982b [0x40, 0x88, 0x79, 0x14] (StorePre 0x10982b 4 (fun s => AddrMode.addr (.base 1 (.d8 0x14)) s (0x10982b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10982b 4 7 (.base 1 (.d8 0x14)))
      [.gpr 7, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x10982b 4 7 (.base 1 (.d8 0x14))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10982b 0x40 (by decide) 7 (.base 1 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x10982f [0x44, 0x88, 0x41, 0x15] (StorePre 0x10982f 4 (fun s => AddrMode.addr (.base 1 (.d8 0x15)) s (0x10982f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10982f 4 8 (.base 1 (.d8 0x15)))
      [.gpr 8, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x10982f 4 8 (.base 1 (.d8 0x15))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10982f 0x44 (by decide) 0 (.base 1 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x109833 [0x44, 0x88, 0x49, 0x16] (StorePre 0x109833 4 (fun s => AddrMode.addr (.base 1 (.d8 0x16)) s (0x109833 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109833 4 9 (.base 1 (.d8 0x16)))
      [.gpr 9, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x109833 4 9 (.base 1 (.d8 0x16))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109833 0x44 (by decide) 1 (.base 1 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f50 : InstrSpec 0x109837 [0x44, 0x88, 0x51, 0x17] (StorePre 0x109837 4 (fun s => AddrMode.addr (.base 1 (.d8 0x17)) s (0x109837 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109837 4 10 (.base 1 (.d8 0x17)))
      [.gpr 10, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x109837 4 10 (.base 1 (.d8 0x17))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109837 0x44 (by decide) 2 (.base 1 (.d8 0x17)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f51 : InstrSpec 0x10983b [0x44, 0x88, 0x59, 0x18] (StorePre 0x10983b 4 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x10983b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10983b 4 11 (.base 1 (.d8 0x18)))
      [.gpr 11, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x10983b 4 11 (.base 1 (.d8 0x18))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10983b 0x44 (by decide) 3 (.base 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x10983f [0x88, 0x59, 0x19] (StorePre 0x10983f 3 (fun s => AddrMode.addr (.base 1 (.d8 0x19)) s (0x10983f + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10983f 3 3 (.base 1 (.d8 0x19)))
      [.gpr 3, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x10983f 3 3 (.base 1 (.d8 0x19))).toInstrSpec (mov_m8_r8_effect_step 0x10983f 3 (by decide) (.base 1 (.d8 0x19)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f53 : InstrSpec 0x109842 [0x40, 0x88, 0x69, 0x1A] (StorePre 0x109842 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1a)) s (0x109842 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109842 4 5 (.base 1 (.d8 0x1a)))
      [.gpr 5, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x109842 4 5 (.base 1 (.d8 0x1a))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109842 0x40 (by decide) 5 (.base 1 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x109846 [0x44, 0x88, 0x71, 0x1B] (StorePre 0x109846 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1b)) s (0x109846 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109846 4 14 (.base 1 (.d8 0x1b)))
      [.gpr 14, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x109846 4 14 (.base 1 (.d8 0x1b))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109846 0x44 (by decide) 6 (.base 1 (.d8 0x1b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f55 : InstrSpec 0x10984a [0x44, 0x88, 0x79, 0x1C] (StorePre 0x10984a 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1c)) s (0x10984a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10984a 4 15 (.base 1 (.d8 0x1c)))
      [.gpr 15, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x10984a 4 15 (.base 1 (.d8 0x1c))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10984a 0x44 (by decide) 7 (.base 1 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x10984e [0x44, 0x88, 0x61, 0x1D] (StorePre 0x10984e 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1d)) s (0x10984e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10984e 4 12 (.base 1 (.d8 0x1d)))
      [.gpr 12, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x10984e 4 12 (.base 1 (.d8 0x1d))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10984e 0x44 (by decide) 4 (.base 1 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f57 : InstrSpec 0x109852 [0x44, 0x88, 0x69, 0x1E] (StorePre 0x109852 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1e)) s (0x109852 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109852 4 13 (.base 1 (.d8 0x1e)))
      [.gpr 13, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x109852 4 13 (.base 1 (.d8 0x1e))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109852 0x44 (by decide) 5 (.base 1 (.d8 0x1e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f58 : InstrSpec 0x109856 [0x88, 0x41, 0x1F] (StorePre 0x109856 3 (fun s => AddrMode.addr (.base 1 (.d8 0x1f)) s (0x109856 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109856 3 0 (.base 1 (.d8 0x1f)))
      [.gpr 0, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x109856 3 0 (.base 1 (.d8 0x1f))).toInstrSpec (mov_m8_r8_effect_step 0x109856 0 (by decide) (.base 1 (.d8 0x1f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f59 : InstrSpec 0x109859 [0x83, 0xBC, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x02] (LoadPre 0x109859 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x109859 + BitVec.ofNat 64 8)) 4) (cmpMImm8Effect 0x109859 8 32 (.sib 4 none 0 (.d32 0xe8)) 0x2)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x109859 8 (.sib 4 none 0 (.d32 0xe8)) 0x2).toInstrSpec (cmp_m32_imm8_effect_step 0x109859 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide) 0x2) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f40 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 119), (1, 126), (2, 2), (3, 95), (4, 4), (5, 99), (6, 128), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109807) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.exec (n := 130) (ρ' := [(0, 119), (1, 126), (2, 2), (3, 95), (4, 4), (5, 99), (6, 128), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10980b) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f42 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 128), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109813) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f43 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 133), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10981b) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.exec (n := 135) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 133), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10981f) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f45 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109827) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.exec (n := 138) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10982b) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 139) (RestInside.exec (n := 139) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10982f) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 140) (RestInside.exec (n := 140) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109833) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 141) (RestInside.exec (n := 141) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109837) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 142) (RestInside.exec (n := 142) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10983b) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 143) (RestInside.exec (n := 143) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10983f) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 144) (RestInside.exec (n := 144) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109842) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 145) (RestInside.exec (n := 145) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109846) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 146) (RestInside.exec (n := 146) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10984a) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 147) (RestInside.exec (n := 147) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10984e) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 148) (RestInside.exec (n := 148) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109852) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 149) (RestInside.exec (n := 149) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109856) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 150) (RestInside.exec (n := 150) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109859) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f59 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (19, 151), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109861) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109739_3 code

theorem rest_l109739_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x109739 bytes_l109739) [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (22, 22), (39, 39), (50, 50), (51, 51)]
      41 0x10979b bytes_l109739_1 b_l109739_1 := by
  have f20 : InstrSpec 0x10979b [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x20] (LoadPre 0x10979b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10979b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10979b 6 11 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x10979b 6 11 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10979b 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x1097a1 [0x44, 0x32, 0x5A, 0x18] (LoadPre 0x1097a1 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1097a1 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1097a1 4 11 (.base 2 (.d8 0x18)))
      [.gpr 11, .gpr 2] [] [.reg 11, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1097a1 4 11 (.base 2 (.d8 0x18))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1097a1 0x44 (by decide) 3 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x1097a5 [0x0F, 0xB6, 0x5C, 0x24, 0x21] (LoadPre 0x1097a5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x21)) s (0x1097a5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1097a5 5 3 (.sib 4 none 0 (.d8 0x21)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x1097a5 5 3 (.sib 4 none 0 (.d8 0x21))).toInstrSpec (movzx_r32_m8_effect_step 0x1097a5 3 (.sib 4 none 0 (.d8 0x21)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x1097aa [0x32, 0x5A, 0x19] (LoadPre 0x1097aa (fun s => AddrMode.addr (.base 2 (.d8 0x19)) s (0x1097aa + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1097aa 3 3 (.base 2 (.d8 0x19)))
      [.gpr 3, .gpr 2] [] [.reg 3, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1097aa 3 3 (.base 2 (.d8 0x19))).toInstrSpec (xor_r8_m8_effect_step 0x1097aa 3 (by decide) (.base 2 (.d8 0x19)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x1097ad [0x0F, 0xB6, 0x6C, 0x24, 0x22] (LoadPre 0x1097ad (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x1097ad + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1097ad 5 5 (.sib 4 none 0 (.d8 0x22)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x1097ad 5 5 (.sib 4 none 0 (.d8 0x22))).toInstrSpec (movzx_r32_m8_effect_step 0x1097ad 5 (.sib 4 none 0 (.d8 0x22)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x1097b2 [0x40, 0x32, 0x6A, 0x1A] (LoadPre 0x1097b2 (fun s => AddrMode.addr (.base 2 (.d8 0x1a)) s (0x1097b2 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1097b2 4 5 (.base 2 (.d8 0x1a)))
      [.gpr 5, .gpr 2] [] [.reg 5, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1097b2 4 5 (.base 2 (.d8 0x1a))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1097b2 0x40 (by decide) 5 (.base 2 (.d8 0x1a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x1097b6 [0x44, 0x0F, 0xB6, 0x74, 0x24, 0x23] (LoadPre 0x1097b6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x23)) s (0x1097b6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1097b6 6 14 (.sib 4 none 0 (.d8 0x23)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x1097b6 6 14 (.sib 4 none 0 (.d8 0x23))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1097b6 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x23)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x1097bc [0x44, 0x32, 0x72, 0x1B] (LoadPre 0x1097bc (fun s => AddrMode.addr (.base 2 (.d8 0x1b)) s (0x1097bc + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1097bc 4 14 (.base 2 (.d8 0x1b)))
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1097bc 4 14 (.base 2 (.d8 0x1b))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1097bc 0x44 (by decide) 6 (.base 2 (.d8 0x1b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x1097c0 [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x24] (LoadPre 0x1097c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1097c0 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1097c0 6 15 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x1097c0 6 15 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1097c0 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x1097c6 [0x44, 0x32, 0x7A, 0x1C] (LoadPre 0x1097c6 (fun s => AddrMode.addr (.base 2 (.d8 0x1c)) s (0x1097c6 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1097c6 4 15 (.base 2 (.d8 0x1c)))
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1097c6 4 15 (.base 2 (.d8 0x1c))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1097c6 0x44 (by decide) 7 (.base 2 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x1097ca [0x44, 0x0F, 0xB6, 0x64, 0x24, 0x25] (LoadPre 0x1097ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x1097ca + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1097ca 6 12 (.sib 4 none 0 (.d8 0x25)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x1097ca 6 12 (.sib 4 none 0 (.d8 0x25))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1097ca 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x1097d0 [0x44, 0x32, 0x62, 0x1D] (LoadPre 0x1097d0 (fun s => AddrMode.addr (.base 2 (.d8 0x1d)) s (0x1097d0 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1097d0 4 12 (.base 2 (.d8 0x1d)))
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1097d0 4 12 (.base 2 (.d8 0x1d))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1097d0 0x44 (by decide) 4 (.base 2 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x1097d4 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x26] (LoadPre 0x1097d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x1097d4 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1097d4 6 13 (.sib 4 none 0 (.d8 0x26)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1097d4 6 13 (.sib 4 none 0 (.d8 0x26))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1097d4 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x26)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x1097da [0x44, 0x32, 0x6A, 0x1E] (LoadPre 0x1097da (fun s => AddrMode.addr (.base 2 (.d8 0x1e)) s (0x1097da + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1097da 4 13 (.base 2 (.d8 0x1e)))
      [.gpr 13, .gpr 2] [] [.reg 13, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1097da 4 13 (.base 2 (.d8 0x1e))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1097da 0x44 (by decide) 5 (.base 2 (.d8 0x1e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f34 : InstrSpec 0x1097de [0x0F, 0xB6, 0x44, 0x24, 0x27] (LoadPre 0x1097de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x1097de + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1097de 5 0 (.sib 4 none 0 (.d8 0x27)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1097de 5 0 (.sib 4 none 0 (.d8 0x27))).toInstrSpec (movzx_r32_m8_effect_step 0x1097de 0 (.sib 4 none 0 (.d8 0x27)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x1097e3 [0x32, 0x42, 0x1F] (LoadPre 0x1097e3 (fun s => AddrMode.addr (.base 2 (.d8 0x1f)) s (0x1097e3 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1097e3 3 0 (.base 2 (.d8 0x1f)))
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1097e3 3 0 (.base 2 (.d8 0x1f))).toInstrSpec (xor_r8_m8_effect_step 0x1097e3 0 (by decide) (.base 2 (.d8 0x1f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x1097e6 [0x48, 0x8B, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x1097e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1097e6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1097e6 1 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1097e6 1 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x1097e6 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x1097ee [0x0F, 0xB6, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x1097ee (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1097ee + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1097ee 8 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x1097ee 8 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (movzx_r32_m8_effect_step 0x1097ee 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f38 : InstrSpec 0x1097f6 [0x40, 0x88, 0x71, 0x10] (StorePre 0x1097f6 4 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x1097f6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1097f6 4 6 (.base 1 (.d8 0x10)))
      [.gpr 6, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x1097f6 4 6 (.base 1 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1097f6 0x40 (by decide) 6 (.base 1 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x1097fa [0x48, 0x8B, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x1097fa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1097fa + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1097fa 1 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1097fa 1 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x1097fa 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f20 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097a1) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f21 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097a5) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f22 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(1, 70), (2, 2), (3, 93), (4, 4), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097aa) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f23 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097ad) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f24 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 97), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097b2) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f25 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097b6) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f26 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (14, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097bc) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f27 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (14, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097c0) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f28 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (14, 103), (15, 105), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097c6) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f29 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097ca) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f30 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 109), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097d0) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f31 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097d4) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f32 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 113), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097da) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f33 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097de) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f34 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 117), (1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097e3) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f35 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 119), (1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097e6) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 119), (1, 121), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097ee) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 119), (1, 121), (2, 2), (3, 95), (4, 4), (5, 99), (6, 123), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097f6) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.exec (n := 125) (ρ' := [(0, 119), (1, 121), (2, 2), (3, 95), (4, 4), (5, 99), (6, 123), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097fa) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f39 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 119), (1, 126), (2, 2), (3, 95), (4, 4), (5, 99), (6, 123), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109802) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109739_2 code

theorem rest_l109739 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109739 bytes_l109739) (entryMap (live .l109739))
      61 0x109739 bytes_l109739 b_l109739 := by
  have f0 : InstrSpec 0x109739 [0x0F, 0xB6, 0x4C, 0x24, 0x18] (LoadPre 0x109739 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109739 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109739 5 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109739 5 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (movzx_r32_m8_effect_step 0x109739 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10973e [0x0F, 0xB6, 0x74, 0x24, 0x19] (LoadPre 0x10973e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x10973e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10973e 5 6 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x10973e 5 6 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (movzx_r32_m8_effect_step 0x10973e 6 (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x109743 [0x32, 0x4A, 0x10] (LoadPre 0x109743 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x109743 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x109743 3 1 (.base 2 (.d8 0x10)))
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x109743 3 1 (.base 2 (.d8 0x10))).toInstrSpec (xor_r8_m8_effect_step 0x109743 1 (by decide) (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x109746 [0x88, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x109746 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109746 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x109746 7 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109746 7 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m8_r8_effect_step 0x109746 1 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10974d [0x40, 0x32, 0x72, 0x11] (LoadPre 0x10974d (fun s => AddrMode.addr (.base 2 (.d8 0x11)) s (0x10974d + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10974d 4 6 (.base 2 (.d8 0x11)))
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10974d 4 6 (.base 2 (.d8 0x11))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10974d 0x40 (by decide) 6 (.base 2 (.d8 0x11)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x109751 [0x40, 0x88, 0x74, 0x24, 0x78] (StorePre 0x109751 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109751 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x109751 5 6 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109751 5 6 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109751 0x40 (by decide) 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x109756 [0x0F, 0xB6, 0x4C, 0x24, 0x1A] (LoadPre 0x109756 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x109756 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109756 5 1 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109756 5 1 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (movzx_r32_m8_effect_step 0x109756 1 (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10975b [0x32, 0x4A, 0x12] (LoadPre 0x10975b (fun s => AddrMode.addr (.base 2 (.d8 0x12)) s (0x10975b + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10975b 3 1 (.base 2 (.d8 0x12)))
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10975b 3 1 (.base 2 (.d8 0x12))).toInstrSpec (xor_r8_m8_effect_step 0x10975b 1 (by decide) (.base 2 (.d8 0x12)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10975e [0x88, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x10975e 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10975e + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10975e 7 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10975e 7 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m8_r8_effect_step 0x10975e 1 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x109765 [0x0F, 0xB6, 0x4C, 0x24, 0x1B] (LoadPre 0x109765 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x109765 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109765 5 1 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109765 5 1 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (movzx_r32_m8_effect_step 0x109765 1 (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x10976a [0x32, 0x4A, 0x13] (LoadPre 0x10976a (fun s => AddrMode.addr (.base 2 (.d8 0x13)) s (0x10976a + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10976a 3 1 (.base 2 (.d8 0x13)))
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10976a 3 1 (.base 2 (.d8 0x13))).toInstrSpec (xor_r8_m8_effect_step 0x10976a 1 (by decide) (.base 2 (.d8 0x13)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10976d [0x88, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x10976d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10976d + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10976d 7 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10976d 7 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m8_r8_effect_step 0x10976d 1 (by decide) (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x109774 [0x0F, 0xB6, 0x7C, 0x24, 0x1C] (LoadPre 0x109774 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x109774 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109774 5 7 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x109774 5 7 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (movzx_r32_m8_effect_step 0x109774 7 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x109779 [0x40, 0x32, 0x7A, 0x14] (LoadPre 0x109779 (fun s => AddrMode.addr (.base 2 (.d8 0x14)) s (0x109779 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109779 4 7 (.base 2 (.d8 0x14)))
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x109779 4 7 (.base 2 (.d8 0x14))).toInstrSpec (xor_r8_m8_rex_effect_step 0x109779 0x40 (by decide) 7 (.base 2 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10977d [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x1D] (LoadPre 0x10977d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x10977d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10977d 6 8 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x10977d 6 8 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10977d 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x109783 [0x44, 0x32, 0x42, 0x15] (LoadPre 0x109783 (fun s => AddrMode.addr (.base 2 (.d8 0x15)) s (0x109783 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109783 4 8 (.base 2 (.d8 0x15)))
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x109783 4 8 (.base 2 (.d8 0x15))).toInstrSpec (xor_r8_m8_rex_effect_step 0x109783 0x44 (by decide) 0 (.base 2 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x109787 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x1E] (LoadPre 0x109787 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x109787 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109787 6 9 (.sib 4 none 0 (.d8 0x1e)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x109787 6 9 (.sib 4 none 0 (.d8 0x1e))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x109787 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10978d [0x44, 0x32, 0x4A, 0x16] (LoadPre 0x10978d (fun s => AddrMode.addr (.base 2 (.d8 0x16)) s (0x10978d + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10978d 4 9 (.base 2 (.d8 0x16)))
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10978d 4 9 (.base 2 (.d8 0x16))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10978d 0x44 (by decide) 1 (.base 2 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x109791 [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x1F] (LoadPre 0x109791 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x109791 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109791 6 10 (.sib 4 none 0 (.d8 0x1f)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x109791 6 10 (.sib 4 none 0 (.d8 0x1f))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x109791 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x109797 [0x44, 0x32, 0x52, 0x17] (LoadPre 0x109797 (fun s => AddrMode.addr (.base 2 (.d8 0x17)) s (0x109797 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109797 4 10 (.base 2 (.d8 0x17)))
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x109797 4 10 (.base 2 (.d8 0x17))).toInstrSpec (xor_r8_m8_rex_effect_step 0x109797 0x44 (by decide) 2 (.base 2 (.d8 0x17)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10973e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 2), (4, 4), (6, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109743) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (2, 2), (4, 4), (6, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109746) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(1, 57), (2, 2), (4, 4), (6, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10974d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 57), (2, 2), (4, 4), (6, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109751) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(1, 57), (2, 2), (4, 4), (6, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109756) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 63), (2, 2), (4, 4), (6, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10975b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 65), (2, 2), (4, 4), (6, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10975e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(1, 65), (2, 2), (4, 4), (6, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109765) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 68), (2, 2), (4, 4), (6, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10976a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10976d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109774) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109779) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10977d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109783) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109787) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 79), (9, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10978d) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 79), (9, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109791) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 79), (9, 83), (10, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109797) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10979b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109739_1 code

theorem block_l109739 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109739 :=
  Rest.liftedBlock (rest_l109739 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109739 x hx)

theorem rest_l109867_2 [Bindings] (code : CodeMap) :
    Rest (n := 128) code lifted (codeRange 0x109867 bytes_l109867) [(0, 55), (1, 120), (2, 125), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]
      15 0x109924 bytes_l109867_2 b_l109867_2 := by
  have f40 : InstrSpec 0x109924 [0x0F, 0xB6, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x109924 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x109924 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x109924 8 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x109924 8 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (movzx_r32_m8_effect_step 0x109924 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x10992c [0x88, 0x50, 0x22] (StorePre 0x10992c 3 (fun s => AddrMode.addr (.base 0 (.d8 0x22)) s (0x10992c + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10992c 3 2 (.base 0 (.d8 0x22)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10992c 3 2 (.base 0 (.d8 0x22))).toInstrSpec (mov_m8_r8_effect_step 0x10992c 2 (by decide) (.base 0 (.d8 0x22)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x10992f [0x40, 0x88, 0x70, 0x23] (StorePre 0x10992f 4 (fun s => AddrMode.addr (.base 0 (.d8 0x23)) s (0x10992f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10992f 4 6 (.base 0 (.d8 0x23)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10992f 4 6 (.base 0 (.d8 0x23))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10992f 0x40 (by decide) 6 (.base 0 (.d8 0x23)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f43 : InstrSpec 0x109933 [0x40, 0x88, 0x78, 0x24] (StorePre 0x109933 4 (fun s => AddrMode.addr (.base 0 (.d8 0x24)) s (0x109933 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109933 4 7 (.base 0 (.d8 0x24)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x109933 4 7 (.base 0 (.d8 0x24))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109933 0x40 (by decide) 7 (.base 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f44 : InstrSpec 0x109937 [0x44, 0x88, 0x40, 0x25] (StorePre 0x109937 4 (fun s => AddrMode.addr (.base 0 (.d8 0x25)) s (0x109937 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109937 4 8 (.base 0 (.d8 0x25)))
      [.gpr 8, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x109937 4 8 (.base 0 (.d8 0x25))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109937 0x44 (by decide) 0 (.base 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x10993b [0x44, 0x88, 0x48, 0x26] (StorePre 0x10993b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x26)) s (0x10993b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10993b 4 9 (.base 0 (.d8 0x26)))
      [.gpr 9, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10993b 4 9 (.base 0 (.d8 0x26))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10993b 0x44 (by decide) 1 (.base 0 (.d8 0x26)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f46 : InstrSpec 0x10993f [0x44, 0x88, 0x50, 0x27] (StorePre 0x10993f 4 (fun s => AddrMode.addr (.base 0 (.d8 0x27)) s (0x10993f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10993f 4 10 (.base 0 (.d8 0x27)))
      [.gpr 10, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10993f 4 10 (.base 0 (.d8 0x27))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10993f 0x44 (by decide) 2 (.base 0 (.d8 0x27)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f47 : InstrSpec 0x109943 [0x44, 0x88, 0x58, 0x28] (StorePre 0x109943 4 (fun s => AddrMode.addr (.base 0 (.d8 0x28)) s (0x109943 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109943 4 11 (.base 0 (.d8 0x28)))
      [.gpr 11, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x109943 4 11 (.base 0 (.d8 0x28))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109943 0x44 (by decide) 3 (.base 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x109947 [0x88, 0x58, 0x29] (StorePre 0x109947 3 (fun s => AddrMode.addr (.base 0 (.d8 0x29)) s (0x109947 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109947 3 3 (.base 0 (.d8 0x29)))
      [.gpr 3, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x109947 3 3 (.base 0 (.d8 0x29))).toInstrSpec (mov_m8_r8_effect_step 0x109947 3 (by decide) (.base 0 (.d8 0x29)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x10994a [0x40, 0x88, 0x68, 0x2A] (StorePre 0x10994a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2a)) s (0x10994a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10994a 4 5 (.base 0 (.d8 0x2a)))
      [.gpr 5, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10994a 4 5 (.base 0 (.d8 0x2a))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10994a 0x40 (by decide) 5 (.base 0 (.d8 0x2a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f50 : InstrSpec 0x10994e [0x44, 0x88, 0x70, 0x2B] (StorePre 0x10994e 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2b)) s (0x10994e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10994e 4 14 (.base 0 (.d8 0x2b)))
      [.gpr 14, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10994e 4 14 (.base 0 (.d8 0x2b))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10994e 0x44 (by decide) 6 (.base 0 (.d8 0x2b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f51 : InstrSpec 0x109952 [0x44, 0x88, 0x78, 0x2C] (StorePre 0x109952 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2c)) s (0x109952 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109952 4 15 (.base 0 (.d8 0x2c)))
      [.gpr 15, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x109952 4 15 (.base 0 (.d8 0x2c))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109952 0x44 (by decide) 7 (.base 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x109956 [0x44, 0x88, 0x60, 0x2D] (StorePre 0x109956 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2d)) s (0x109956 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109956 4 12 (.base 0 (.d8 0x2d)))
      [.gpr 12, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x109956 4 12 (.base 0 (.d8 0x2d))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109956 0x44 (by decide) 4 (.base 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f53 : InstrSpec 0x10995a [0x44, 0x88, 0x68, 0x2E] (StorePre 0x10995a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2e)) s (0x10995a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10995a 4 13 (.base 0 (.d8 0x2e)))
      [.gpr 13, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10995a 4 13 (.base 0 (.d8 0x2e))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10995a 0x44 (by decide) 5 (.base 0 (.d8 0x2e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x10995e [0x88, 0x48, 0x2F] (StorePre 0x10995e 3 (fun s => AddrMode.addr (.base 0 (.d8 0x2f)) s (0x10995e + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10995e 3 1 (.base 0 (.d8 0x2f)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10995e 3 1 (.base 0 (.d8 0x2f))).toInstrSpec (mov_m8_r8_effect_step 0x10995e 1 (by decide) (.base 0 (.d8 0x2f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f40 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10992c) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.exec (n := 130) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10992f) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 131) (RestInside.exec (n := 131) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109933) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 132) (RestInside.exec (n := 132) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109937) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 133) (RestInside.exec (n := 133) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10993b) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 134) (RestInside.exec (n := 134) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10993f) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 135) (RestInside.exec (n := 135) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109943) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 136) (RestInside.exec (n := 136) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109947) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 137) (RestInside.exec (n := 137) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10994a) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 138) (RestInside.exec (n := 138) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10994e) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 139) (RestInside.exec (n := 139) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109952) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 140) (RestInside.exec (n := 140) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109956) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 141) (RestInside.exec (n := 141) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10995a) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 142) (RestInside.exec (n := 142) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10995e) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 143) (RestInside.exec (n := 143) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109961) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 144) (by decide) rfl

theorem rest_l109867_1 [Bindings] (code : CodeMap) :
    Rest (n := 90) code lifted (codeRange 0x109867 bytes_l109867) [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (22, 22), (39, 39), (50, 50), (51, 51)]
      35 0x1098c6 bytes_l109867_1 b_l109867_1 := by
  have f20 : InstrSpec 0x1098c6 [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x30] (LoadPre 0x1098c6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1098c6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1098c6 6 11 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x1098c6 6 11 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1098c6 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x1098cc [0x44, 0x32, 0x5A, 0x28] (LoadPre 0x1098cc (fun s => AddrMode.addr (.base 2 (.d8 0x28)) s (0x1098cc + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098cc 4 11 (.base 2 (.d8 0x28)))
      [.gpr 11, .gpr 2] [] [.reg 11, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1098cc 4 11 (.base 2 (.d8 0x28))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1098cc 0x44 (by decide) 3 (.base 2 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x1098d0 [0x0F, 0xB6, 0x5C, 0x24, 0x31] (LoadPre 0x1098d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x1098d0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1098d0 5 3 (.sib 4 none 0 (.d8 0x31)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x1098d0 5 3 (.sib 4 none 0 (.d8 0x31))).toInstrSpec (movzx_r32_m8_effect_step 0x1098d0 3 (.sib 4 none 0 (.d8 0x31)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x1098d5 [0x32, 0x5A, 0x29] (LoadPre 0x1098d5 (fun s => AddrMode.addr (.base 2 (.d8 0x29)) s (0x1098d5 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1098d5 3 3 (.base 2 (.d8 0x29)))
      [.gpr 3, .gpr 2] [] [.reg 3, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1098d5 3 3 (.base 2 (.d8 0x29))).toInstrSpec (xor_r8_m8_effect_step 0x1098d5 3 (by decide) (.base 2 (.d8 0x29)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x1098d8 [0x0F, 0xB6, 0x6C, 0x24, 0x32] (LoadPre 0x1098d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x1098d8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1098d8 5 5 (.sib 4 none 0 (.d8 0x32)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x1098d8 5 5 (.sib 4 none 0 (.d8 0x32))).toInstrSpec (movzx_r32_m8_effect_step 0x1098d8 5 (.sib 4 none 0 (.d8 0x32)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x1098dd [0x40, 0x32, 0x6A, 0x2A] (LoadPre 0x1098dd (fun s => AddrMode.addr (.base 2 (.d8 0x2a)) s (0x1098dd + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098dd 4 5 (.base 2 (.d8 0x2a)))
      [.gpr 5, .gpr 2] [] [.reg 5, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1098dd 4 5 (.base 2 (.d8 0x2a))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1098dd 0x40 (by decide) 5 (.base 2 (.d8 0x2a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x1098e1 [0x44, 0x0F, 0xB6, 0x74, 0x24, 0x33] (LoadPre 0x1098e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x33)) s (0x1098e1 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1098e1 6 14 (.sib 4 none 0 (.d8 0x33)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x1098e1 6 14 (.sib 4 none 0 (.d8 0x33))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1098e1 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x33)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x1098e7 [0x44, 0x32, 0x72, 0x2B] (LoadPre 0x1098e7 (fun s => AddrMode.addr (.base 2 (.d8 0x2b)) s (0x1098e7 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098e7 4 14 (.base 2 (.d8 0x2b)))
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1098e7 4 14 (.base 2 (.d8 0x2b))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1098e7 0x44 (by decide) 6 (.base 2 (.d8 0x2b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x1098eb [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x34] (LoadPre 0x1098eb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x1098eb + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1098eb 6 15 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x1098eb 6 15 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1098eb 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x1098f1 [0x44, 0x32, 0x7A, 0x2C] (LoadPre 0x1098f1 (fun s => AddrMode.addr (.base 2 (.d8 0x2c)) s (0x1098f1 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098f1 4 15 (.base 2 (.d8 0x2c)))
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1098f1 4 15 (.base 2 (.d8 0x2c))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1098f1 0x44 (by decide) 7 (.base 2 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x1098f5 [0x44, 0x0F, 0xB6, 0x64, 0x24, 0x35] (LoadPre 0x1098f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x1098f5 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1098f5 6 12 (.sib 4 none 0 (.d8 0x35)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x1098f5 6 12 (.sib 4 none 0 (.d8 0x35))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1098f5 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x35)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x1098fb [0x44, 0x32, 0x62, 0x2D] (LoadPre 0x1098fb (fun s => AddrMode.addr (.base 2 (.d8 0x2d)) s (0x1098fb + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098fb 4 12 (.base 2 (.d8 0x2d)))
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1098fb 4 12 (.base 2 (.d8 0x2d))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1098fb 0x44 (by decide) 4 (.base 2 (.d8 0x2d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x1098ff [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x36] (LoadPre 0x1098ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x1098ff + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1098ff 6 13 (.sib 4 none 0 (.d8 0x36)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1098ff 6 13 (.sib 4 none 0 (.d8 0x36))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1098ff 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x36)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x109905 [0x44, 0x32, 0x6A, 0x2E] (LoadPre 0x109905 (fun s => AddrMode.addr (.base 2 (.d8 0x2e)) s (0x109905 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109905 4 13 (.base 2 (.d8 0x2e)))
      [.gpr 13, .gpr 2] [] [.reg 13, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x109905 4 13 (.base 2 (.d8 0x2e))).toInstrSpec (xor_r8_m8_rex_effect_step 0x109905 0x44 (by decide) 5 (.base 2 (.d8 0x2e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f34 : InstrSpec 0x109909 [0x0F, 0xB6, 0x4C, 0x24, 0x37] (LoadPre 0x109909 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x37)) s (0x109909 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109909 5 1 (.sib 4 none 0 (.d8 0x37)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109909 5 1 (.sib 4 none 0 (.d8 0x37))).toInstrSpec (movzx_r32_m8_effect_step 0x109909 1 (.sib 4 none 0 (.d8 0x37)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x10990e [0x32, 0x4A, 0x2F] (LoadPre 0x10990e (fun s => AddrMode.addr (.base 2 (.d8 0x2f)) s (0x10990e + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10990e 3 1 (.base 2 (.d8 0x2f)))
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10990e 3 1 (.base 2 (.d8 0x2f))).toInstrSpec (xor_r8_m8_effect_step 0x10990e 1 (by decide) (.base 2 (.d8 0x2f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x109911 [0x0F, 0xB6, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x109911 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109911 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x109911 8 2 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x109911 8 2 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (movzx_r32_m8_effect_step 0x109911 2 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x109919 [0x88, 0x50, 0x20] (StorePre 0x109919 3 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x109919 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109919 3 2 (.base 0 (.d8 0x20)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x109919 3 2 (.base 0 (.d8 0x20))).toInstrSpec (mov_m8_r8_effect_step 0x109919 2 (by decide) (.base 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x10991c [0x0F, 0xB6, 0x54, 0x24, 0x78] (LoadPre 0x10991c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10991c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10991c 5 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x10991c 5 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (movzx_r32_m8_effect_step 0x10991c 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x109921 [0x88, 0x50, 0x21] (StorePre 0x109921 3 (fun s => AddrMode.addr (.base 0 (.d8 0x21)) s (0x109921 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109921 3 2 (.base 0 (.d8 0x21)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x109921 3 2 (.base 0 (.d8 0x21))).toInstrSpec (mov_m8_r8_effect_step 0x109921 2 (by decide) (.base 0 (.d8 0x21)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f20 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098cc) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f21 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098d0) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f22 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 94), (4, 4), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098d5) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f23 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098d8) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f24 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 98), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098dd) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f25 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098e1) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f26 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (14, 102), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098e7) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f27 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (14, 104), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098eb) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f28 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (14, 104), (15, 106), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098f1) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f29 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098f5) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f30 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 110), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098fb) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f31 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098ff) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f32 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 114), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109905) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f33 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109909) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f34 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 55), (1, 118), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10990e) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f35 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 55), (1, 120), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109911) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f36 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 55), (1, 120), (2, 122), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109919) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.exec (n := 124) (ρ' := [(0, 55), (1, 120), (2, 122), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10991c) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f38 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 55), (1, 120), (2, 125), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109921) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.exec (n := 127) (ρ' := [(0, 55), (1, 120), (2, 125), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109924) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l109867_2 code

theorem rest_l109867 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109867 bytes_l109867) (entryMap (live .l109867))
      55 0x109867 bytes_l109867 b_l109867 := by
  have f0 : InstrSpec 0x109867 [0x0F, 0xB6, 0x74, 0x24, 0x28] (LoadPre 0x109867 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109867 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109867 5 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x109867 5 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (movzx_r32_m8_effect_step 0x109867 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10986c [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x10986c) (movR64R64Effect 0x10986c 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10986c 0 1).toInstrSpec (mov_r64_r64_effect_step 0x10986c 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10986f [0x0F, 0xB6, 0x4C, 0x24, 0x29] (LoadPre 0x10986f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x29)) s (0x10986f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10986f 5 1 (.sib 4 none 0 (.d8 0x29)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10986f 5 1 (.sib 4 none 0 (.d8 0x29))).toInstrSpec (movzx_r32_m8_effect_step 0x10986f 1 (.sib 4 none 0 (.d8 0x29)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x109874 [0x40, 0x32, 0x72, 0x20] (LoadPre 0x109874 (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x109874 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109874 4 6 (.base 2 (.d8 0x20)))
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x109874 4 6 (.base 2 (.d8 0x20))).toInstrSpec (xor_r8_m8_rex_effect_step 0x109874 0x40 (by decide) 6 (.base 2 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x109878 [0x40, 0x88, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x109878 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109878 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x109878 8 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109878 8 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109878 0x40 (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x109880 [0x32, 0x4A, 0x21] (LoadPre 0x109880 (fun s => AddrMode.addr (.base 2 (.d8 0x21)) s (0x109880 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x109880 3 1 (.base 2 (.d8 0x21)))
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x109880 3 1 (.base 2 (.d8 0x21))).toInstrSpec (xor_r8_m8_effect_step 0x109880 1 (by decide) (.base 2 (.d8 0x21)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x109883 [0x88, 0x4C, 0x24, 0x78] (StorePre 0x109883 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109883 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109883 4 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109883 4 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m8_r8_effect_step 0x109883 1 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x109887 [0x0F, 0xB6, 0x4C, 0x24, 0x2A] (LoadPre 0x109887 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x109887 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109887 5 1 (.sib 4 none 0 (.d8 0x2a)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109887 5 1 (.sib 4 none 0 (.d8 0x2a))).toInstrSpec (movzx_r32_m8_effect_step 0x109887 1 (.sib 4 none 0 (.d8 0x2a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10988c [0x32, 0x4A, 0x22] (LoadPre 0x10988c (fun s => AddrMode.addr (.base 2 (.d8 0x22)) s (0x10988c + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10988c 3 1 (.base 2 (.d8 0x22)))
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10988c 3 1 (.base 2 (.d8 0x22))).toInstrSpec (xor_r8_m8_effect_step 0x10988c 1 (by decide) (.base 2 (.d8 0x22)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10988f [0x88, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x10988f 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10988f + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10988f 7 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10988f 7 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m8_r8_effect_step 0x10988f 1 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x109896 [0x0F, 0xB6, 0x74, 0x24, 0x2B] (LoadPre 0x109896 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2b)) s (0x109896 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109896 5 6 (.sib 4 none 0 (.d8 0x2b)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x109896 5 6 (.sib 4 none 0 (.d8 0x2b))).toInstrSpec (movzx_r32_m8_effect_step 0x109896 6 (.sib 4 none 0 (.d8 0x2b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10989b [0x40, 0x32, 0x72, 0x23] (LoadPre 0x10989b (fun s => AddrMode.addr (.base 2 (.d8 0x23)) s (0x10989b + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10989b 4 6 (.base 2 (.d8 0x23)))
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10989b 4 6 (.base 2 (.d8 0x23))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10989b 0x40 (by decide) 6 (.base 2 (.d8 0x23)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x10989f [0x0F, 0xB6, 0x7C, 0x24, 0x2C] (LoadPre 0x10989f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x10989f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10989f 5 7 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x10989f 5 7 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (movzx_r32_m8_effect_step 0x10989f 7 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1098a4 [0x40, 0x32, 0x7A, 0x24] (LoadPre 0x1098a4 (fun s => AddrMode.addr (.base 2 (.d8 0x24)) s (0x1098a4 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098a4 4 7 (.base 2 (.d8 0x24)))
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1098a4 4 7 (.base 2 (.d8 0x24))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1098a4 0x40 (by decide) 7 (.base 2 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1098a8 [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x2D] (LoadPre 0x1098a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x1098a8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1098a8 6 8 (.sib 4 none 0 (.d8 0x2d)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x1098a8 6 8 (.sib 4 none 0 (.d8 0x2d))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1098a8 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1098ae [0x44, 0x32, 0x42, 0x25] (LoadPre 0x1098ae (fun s => AddrMode.addr (.base 2 (.d8 0x25)) s (0x1098ae + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098ae 4 8 (.base 2 (.d8 0x25)))
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1098ae 4 8 (.base 2 (.d8 0x25))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1098ae 0x44 (by decide) 0 (.base 2 (.d8 0x25)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x1098b2 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x2E] (LoadPre 0x1098b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2e)) s (0x1098b2 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1098b2 6 9 (.sib 4 none 0 (.d8 0x2e)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x1098b2 6 9 (.sib 4 none 0 (.d8 0x2e))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1098b2 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x2e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x1098b8 [0x44, 0x32, 0x4A, 0x26] (LoadPre 0x1098b8 (fun s => AddrMode.addr (.base 2 (.d8 0x26)) s (0x1098b8 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098b8 4 9 (.base 2 (.d8 0x26)))
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1098b8 4 9 (.base 2 (.d8 0x26))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1098b8 0x44 (by decide) 1 (.base 2 (.d8 0x26)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x1098bc [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x2F] (LoadPre 0x1098bc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2f)) s (0x1098bc + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1098bc 6 10 (.sib 4 none 0 (.d8 0x2f)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x1098bc 6 10 (.sib 4 none 0 (.d8 0x2f))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1098bc 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x2f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x1098c2 [0x44, 0x32, 0x52, 0x27] (LoadPre 0x1098c2 (fun s => AddrMode.addr (.base 2 (.d8 0x27)) s (0x1098c2 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098c2 4 10 (.base 2 (.d8 0x27)))
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1098c2 4 10 (.base 2 (.d8 0x27))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1098c2 0x44 (by decide) 2 (.base 2 (.d8 0x27)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (6, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10986c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (6, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10986f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (2, 2), (4, 4), (6, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109874) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 57), (2, 2), (4, 4), (6, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109878) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 57), (2, 2), (4, 4), (6, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109880) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 62), (2, 2), (4, 4), (6, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109883) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 62), (2, 2), (4, 4), (6, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109887) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 65), (2, 2), (4, 4), (6, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10988c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10988f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109896) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10989b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10989f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098a4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098a8) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098ae) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098b2) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 80), (9, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098b8) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 80), (9, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098bc) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f18 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 80), (9, 84), (10, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098c2) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f19 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098c6) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109867_1 code

theorem block_l109867 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109867 :=
  Rest.liftedBlock (rest_l109867 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109867 x hx)

theorem rest_l109961 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109961 bytes_l109961) (entryMap (live .l109961))
      8 0x109961 bytes_l109961 b_l109961 := by
  have f0 : InstrSpec 0x109961 [0x48, 0x81, 0xC4, 0xD8, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x109961) (addR64Imm32Effect 0x109961 4 0x8d8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x109961 4 0x8d8).toInstrSpec (add_r64_imm32_effect_step 0x109961 0x48 0xc4 0x8d8 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x109968 [0x5B] (PopPre 0x109968) (popR64Effect 0x109968 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109968 1 3).toInstrSpec (pop_r64_effect_step 0x109968 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x109969 [0x41, 0x5C] (PopPre 0x109969) (popR64Effect 0x109969 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109969 2 12).toInstrSpec (pop_r64_rex_effect_step 0x109969 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10996b [0x41, 0x5D] (PopPre 0x10996b) (popR64Effect 0x10996b 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10996b 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10996b 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10996d [0x41, 0x5E] (PopPre 0x10996d) (popR64Effect 0x10996d 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10996d 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10996d 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10996f [0x41, 0x5F] (PopPre 0x10996f) (popR64Effect 0x10996f 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10996f 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10996f 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x109971 [0x5D] (PopPre 0x109971) (popR64Effect 0x109971 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109971 1 5).toInstrSpec (pop_r64_effect_step 0x109971 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x109972 [0xC3] (RetPre 0x109972) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x109972).toInstrSpec (ret_effect_step 0x109972) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109968) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109969) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10996b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10996d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10996f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109971) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109972) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l109961 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109961 :=
  Rest.liftedBlock (rest_l109961 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109961 x hx)

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

theorem_by block_l1084e0_eval :
    program.runBlock (dialect code) ⟨.l1084e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108520_eval :
    program.runBlock (dialect code) ⟨.l108520, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10856d_eval :
    program.runBlock (dialect code) ⟨.l10856d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108590_eval :
    program.runBlock (dialect code) ⟨.l108590, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1085da_eval :
    program.runBlock (dialect code) ⟨.l1085da, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108600_eval :
    program.runBlock (dialect code) ⟨.l108600, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108728_eval :
    program.runBlock (dialect code) ⟨.l108728, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108e98_eval :
    program.runBlock (dialect code) ⟨.l108e98, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108fa2_eval :
    program.runBlock (dialect code) ⟨.l108fa2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109010_eval :
    program.runBlock (dialect code) ⟨.l109010, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10902f_eval :
    program.runBlock (dialect code) ⟨.l10902f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109037_eval :
    program.runBlock (dialect code) ⟨.l109037, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1090d1_eval :
    program.runBlock (dialect code) ⟨.l1090d1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1090e0_eval :
    program.runBlock (dialect code) ⟨.l1090e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109326_eval :
    program.runBlock (dialect code) ⟨.l109326, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10932e_eval :
    program.runBlock (dialect code) ⟨.l10932e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1093a3_eval :
    program.runBlock (dialect code) ⟨.l1093a3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109509_eval :
    program.runBlock (dialect code) ⟨.l109509, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10956a_eval :
    program.runBlock (dialect code) ⟨.l10956a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1095b0_eval :
    program.runBlock (dialect code) ⟨.l1095b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1095ed_eval :
    program.runBlock (dialect code) ⟨.l1095ed, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109618_eval :
    program.runBlock (dialect code) ⟨.l109618, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109739_eval :
    program.runBlock (dialect code) ⟨.l109739, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109867_eval :
    program.runBlock (dialect code) ⟨.l109867, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109961_eval :
    program.runBlock (dialect code) ⟨.l109961, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
