import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l107050 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107050 bytes_l107050) (entryMap (live .l107050))
      14 0x107050 bytes_l107050 b_l107050 := by
  have f0 : InstrSpec 0x107050 [0x55] (PushPre 0x107050 1) (pushR64Effect 0x107050 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107050 1 5).toInstrSpec (push_r64_effect_step 0x107050 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x107051 [0x41, 0x57] (PushPre 0x107051 2) (pushR64Effect 0x107051 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107051 2 15).toInstrSpec (push_r64_rex_effect_step 0x107051 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x107053 [0x41, 0x56] (PushPre 0x107053 2) (pushR64Effect 0x107053 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107053 2 14).toInstrSpec (push_r64_rex_effect_step 0x107053 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x107055 [0x41, 0x55] (PushPre 0x107055 2) (pushR64Effect 0x107055 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107055 2 13).toInstrSpec (push_r64_rex_effect_step 0x107055 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x107057 [0x41, 0x54] (PushPre 0x107057 2) (pushR64Effect 0x107057 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107057 2 12).toInstrSpec (push_r64_rex_effect_step 0x107057 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x107059 [0x53] (PushPre 0x107059 1) (pushR64Effect 0x107059 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107059 1 3).toInstrSpec (push_r64_effect_step 0x107059 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10705a [0x48, 0x81, 0xEC, 0xD8, 0x06, 0x00, 0x00] (fun s => s.RIP = 0x10705a) (subR64Imm32Effect 0x10705a 4 0x6d8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10705a 4 0x6d8).toInstrSpec (sub_r64_imm32_effect_step 0x10705a 0x48 0xec 0x6d8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x107061 [0x48, 0x89, 0xF3] (fun s => s.RIP = 0x107061) (movR64R64Effect 0x107061 3 6)
      [.gpr 6] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x107061 3 6).toInstrSpec (mov_r64_r64_effect_step 0x107061 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x107064 [0x48, 0x8B, 0x07] (LoadPre 0x107064 (fun s => AddrMode.addr (.base 7 .none) s (0x107064 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x107064 0 (.base 7 .none))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107064 0 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x107064 0x48 (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x107067 [0x31, 0xC9] (fun s => s.RIP = 0x107067) (xorR32R32Effect 0x107067 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x107067 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x107067 0xc9 (by decide)) pre_rip
  have f10 : InstrSpec 0x107069 [0x48, 0xBA, 0x00, 0x10, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107069) (movR64Imm64Effect 0x107069 2 0x1000001000)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x107069 2 0x1000001000).toInstrSpec (mov_r64_imm64_effect_step 0x107069 0x48 0xba (by decide) (by decide) 0x1000001000) pre_rip
  have f11 : InstrSpec 0x107073 [0x48, 0xBE, 0x0F, 0x00, 0x0F, 0x00, 0x0F, 0x00, 0x0F, 0x00] (fun s => s.RIP = 0x107073) (movR64Imm64Effect 0x107073 6 0xf000f000f000f)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x107073 6 0xf000f000f000f).toInstrSpec (mov_r64_imm64_effect_step 0x107073 0x48 0xbe (by decide) (by decide) 0xf000f000f000f) pre_rip
  have f12 : InstrSpec 0x10707d [0x48, 0xBF, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11] (fun s => s.RIP = 0x10707d) (movR64Imm64Effect 0x10707d 7 0x1111111111111111)
      [] [] [.reg 7, .rip] :=
    (movR64Imm64Effect_footprint 0x10707d 7 0x1111111111111111).toInstrSpec (mov_r64_imm64_effect_step 0x10707d 0x48 0xbf (by decide) (by decide) 0x1111111111111111) pre_rip
  have f13 : InstrSpec 0x107087 [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107087) (fun _ => nopEffect 0x107087 9)
      [] [] [.rip] :=
    (nopEffect_footprint 0x107087 9).toInstrSpec (nop_m_effect_step 0x107087 [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107051) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107053) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107055) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107057) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107059) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10705a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107061) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107064) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107067) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 71), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107069) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 69), (1, 71), (2, 73), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107073) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 69), (1, 71), (2, 73), (3, 67), (4, 65), (5, 5), (6, 75), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10707d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 69), (1, 71), (2, 73), (3, 67), (4, 65), (5, 5), (6, 75), (7, 77), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107087) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 69), (1, 71), (2, 73), (3, 67), (4, 65), (5, 5), (6, 75), (7, 77), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107090) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 80) (by decide) rfl

theorem block_l107050 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107050 :=
  Rest.liftedBlock (rest_l107050 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107050 x hx)

theorem rest_l107090_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x107090 bytes_l107090) [(0, 0), (1, 88), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 85), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x1070db bytes_l107090_1 b_l107090_1 := by
  exact Rest.jcc (n := 92) (jcc_rel8_effect_step 0x1070db 5 0xb3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l107090 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107090 bytes_l107090) (entryMap (live .l107090))
      21 0x107090 bytes_l107090 b_l107090 := by
  have f0 : InstrSpec 0x107090 [0x44, 0x0F, 0xB7, 0x04, 0x48] (LoadPre 0x107090 (fun s => AddrMode.addr (.sib 0 (some 1) 1 .none) s (0x107090 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x107090 5 8 (.sib 0 (some 1) 1 .none))
      [.gpr 0, .gpr 1] [] [.reg 8, .rip] :=
    (movzxR32M16Effect_footprint 0x107090 5 8 (.sib 0 (some 1) 1 .none)).toInstrSpec (movzx_r32_m16_rex_effect_step 0x107090 0x44 (by decide) 0 (.sib 0 (some 1) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107095 [0x4D, 0x89, 0xC1] (fun s => s.RIP = 0x107095) (movR64R64Effect 0x107095 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x107095 9 8).toInstrSpec (mov_r64_r64_effect_step 0x107095 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x107098 [0x49, 0xC1, 0xE1, 0x18] (fun s => s.RIP = 0x107098) (shlR64Effect 0x107098 4 9 24)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR64Effect_footprint 0x107098 4 9 24).toInstrSpec (shl_r64_imm8_effect_step 0x107098 0x49 0xe1 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10709c [0x4D, 0x09, 0xC1] (fun s => s.RIP = 0x10709c) (orR64R64Effect 0x10709c 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10709c 9 8).toInstrSpec (or_r64_r64_effect_step 0x10709c 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10709f [0x4C, 0x0F, 0xAF, 0xC2] (fun s => s.RIP = 0x10709f) (imulR64R64Effect 0x10709f 4 8 2)
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x10709f 4 8 2).toInstrSpec (imul_r64_r64_effect_step 0x10709f 0x4c (by decide) 0xc2 (by decide)) pre_rip
  have f5 : InstrSpec 0x1070a3 [0x4D, 0x09, 0xC8] (fun s => s.RIP = 0x1070a3) (orR64R64Effect 0x1070a3 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1070a3 8 9).toInstrSpec (or_r64_r64_effect_step 0x1070a3 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1070a6 [0x49, 0x21, 0xF0] (fun s => s.RIP = 0x1070a6) (andR64R64Effect 0x1070a6 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1070a6 8 6).toInstrSpec (and_r64_r64_effect_step 0x1070a6 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1070a9 [0x4D, 0x89, 0xC1] (fun s => s.RIP = 0x1070a9) (movR64R64Effect 0x1070a9 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x1070a9 9 8).toInstrSpec (mov_r64_r64_effect_step 0x1070a9 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1070ac [0x49, 0xC1, 0xE1, 0x06] (fun s => s.RIP = 0x1070ac) (shlR64Effect 0x1070ac 4 9 6)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR64Effect_footprint 0x1070ac 4 9 6).toInstrSpec (shl_r64_imm8_effect_step 0x1070ac 0x49 0xe1 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1070b0 [0x4D, 0x09, 0xC1] (fun s => s.RIP = 0x1070b0) (orR64R64Effect 0x1070b0 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1070b0 9 8).toInstrSpec (or_r64_r64_effect_step 0x1070b0 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1070b3 [0x4D, 0x89, 0xC2] (fun s => s.RIP = 0x1070b3) (movR64R64Effect 0x1070b3 10 8)
      [.gpr 8] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1070b3 10 8).toInstrSpec (mov_r64_r64_effect_step 0x1070b3 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1070b6 [0x49, 0xC1, 0xE2, 0x09] (fun s => s.RIP = 0x1070b6) (shlR64Effect 0x1070b6 4 10 9)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR64Effect_footprint 0x1070b6 4 10 9).toInstrSpec (shl_r64_imm8_effect_step 0x1070b6 0x49 0xe2 0x9 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1070ba [0x4F, 0x8D, 0x04, 0xC2] (fun s => s.RIP = 0x1070ba) (leaR64Effect 0x1070ba 8 (.sib 10 (some 8) 3 .none))
      [.gpr 10, .gpr 8] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x1070ba 8 (.sib 10 (some 8) 3 .none)).toInstrSpec (lea_r64_effect_step 0x1070ba 0x4f (by decide) 0 (.sib 10 (some 8) 3 .none) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1070be [0x4D, 0x09, 0xC8] (fun s => s.RIP = 0x1070be) (orR64R64Effect 0x1070be 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1070be 8 9).toInstrSpec (or_r64_r64_effect_step 0x1070be 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1070c1 [0x49, 0x21, 0xF8] (fun s => s.RIP = 0x1070c1) (andR64R64Effect 0x1070c1 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1070c1 8 7).toInstrSpec (and_r64_r64_effect_step 0x1070c1 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1070c4 [0x4F, 0x8D, 0x04, 0x80] (fun s => s.RIP = 0x1070c4) (leaR64Effect 0x1070c4 8 (.sib 8 (some 8) 2 .none))
      [.gpr 8, .gpr 8] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x1070c4 8 (.sib 8 (some 8) 2 .none)).toInstrSpec (lea_r64_effect_step 0x1070c4 0x4f (by decide) 0 (.sib 8 (some 8) 2 .none) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1070c8 [0x4F, 0x8D, 0x04, 0x40] (fun s => s.RIP = 0x1070c8) (leaR64Effect 0x1070c8 8 (.sib 8 (some 8) 1 .none))
      [.gpr 8, .gpr 8] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x1070c8 8 (.sib 8 (some 8) 1 .none)).toInstrSpec (lea_r64_effect_step 0x1070c8 0x4f (by decide) 0 (.sib 8 (some 8) 1 .none) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1070cc [0x4C, 0x89, 0x84, 0xCC, 0x18, 0x04, 0x00, 0x00] (StorePre 0x1070cc 8 (fun s => AddrMode.addr (.sib 4 (some 1) 3 (.d32 0x418)) s (0x1070cc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1070cc 8 (.sib 4 (some 1) 3 (.d32 0x418)))
      [.gpr 8, .gpr 4, .gpr 1] [] [.rip] :=
    (movM64R64Effect_footprint 0x1070cc 8 (.sib 4 (some 1) 3 (.d32 0x418))).toInstrSpec (mov_m64_r64_effect_step 0x1070cc 0x4c (by decide) 0 (.sib 4 (some 1) 3 (.d32 0x418)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1070d4 [0x48, 0xFF, 0xC1] (fun s => s.RIP = 0x1070d4) (incR64Effect 0x1070d4 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (incR64Effect_footprint 0x1070d4 1).toInstrSpec (inc_r64_effect_step 0x1070d4 0x48 0xc1 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1070d7 [0x48, 0x83, 0xF9, 0x58] (fun s => s.RIP = 0x1070d7) (cmpR64Imm8Effect 0x1070d7 1 0x58)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1070d7 1 0x58).toInstrSpec (cmp_r64_imm8_effect_step 0x1070d7 0x48 0xf9 0x58 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107095) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107098) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10709c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10709f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 61), (9, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070a3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070a6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070a9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 67), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070ac) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070b0) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070b3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 71), (10, 73), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070b6) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070ba) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 77), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070be) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 79), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070c1) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 81), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070c4) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 83), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070c8) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 85), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070cc) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 85), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070d4) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 88), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 85), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070d7) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 0), (1, 88), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 85), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070db) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107090_1 code

theorem block_l107090 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107090 :=
  Rest.liftedBlock (rest_l107090 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107090 x hx)

theorem rest_l1070dd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1070dd bytes_l1070dd) (entryMap (live .l1070dd))
      5 0x1070dd bytes_l1070dd b_l1070dd := by
  have f0 : InstrSpec 0x1070dd [0x48, 0x89, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00] (StorePre 0x1070dd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x1070dd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1070dd 0 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1070dd 0 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (mov_m64_r64_effect_step 0x1070dd 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1070e5 [0x48, 0x8D, 0xBC, 0x24, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1070e5) (leaR64Effect 0x1070e5 7 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1070e5 7 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (lea_r64_effect_step 0x1070e5 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1070ed [0x48, 0x8D, 0xB4, 0x24, 0x18, 0x04, 0x00, 0x00] (fun s => s.RIP = 0x1070ed) (leaR64Effect 0x1070ed 6 (.sib 4 none 0 (.d32 0x418)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1070ed 6 (.sib 4 none 0 (.d32 0x418))).toInstrSpec (lea_r64_effect_step 0x1070ed 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x418)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1070f5 [0xBA, 0xC0, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x1070f5) (movR32Imm32Effect 0x1070f5 5 2 0x2c0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1070f5 5 2 0x2c0).toInstrSpec (mov_r32_imm32_effect_step 0x1070f5 0xba (by decide) 0x2c0) pre_rip
  have f4 : InstrSpec 0x1070fa [0xFF, 0x15, 0x08, 0xA1, 0x0F, 0x00] (GoesTo (CallMemPre 0x1070fa (.rip 0xfa108)) (callEffect (callMemPtr 0x1070fa (.rip 0xfa108)) (0x1070fa + BitVec.ofNat 64 (callMemLen (.rip 0xfa108)))) 0x103f00) (callEffect (callMemPtr 0x1070fa (.rip 0xfa108)) (0x1070fa + BitVec.ofNat 64 (callMemLen (.rip 0xfa108))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1070fa (.rip 0xfa108)).toInstrSpec (call_m64_effect_step 0x1070fa (.rip 0xfa108) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070e5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 54), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070ed) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 56), (7, 54), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070f5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 58), (3, 3), (4, 4), (5, 5), (6, 56), (7, 54), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070fa) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 58), (3, 3), (4, 60), (5, 5), (6, 56), (7, 54), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l1070dd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1070dd :=
  Rest.liftedBlock (rest_l1070dd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1070dd x hx)

theorem rest_l107100 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107100 bytes_l107100) (entryMap (live .l107100))
      14 0x107100 bytes_l107100 b_l107100 := by
  have f0 : InstrSpec 0x107100 [0x4C, 0x8B, 0x0B] (LoadPre 0x107100 (fun s => AddrMode.addr (.base 3 .none) s (0x107100 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x107100 9 (.base 3 .none))
      [.gpr 3] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x107100 9 (.base 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x107100 0x4c (by decide) 1 (.base 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107103 [0x48, 0x8B, 0x43, 0x08] (LoadPre 0x107103 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x107103 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107103 0 (.base 3 (.d8 0x8)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107103 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x107103 0x48 (by decide) 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x107107 [0x48, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00] (StorePre 0x107107 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x107107 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107107 0 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107107 0 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x107107 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10710f [0x48, 0x8B, 0x53, 0x10] (LoadPre 0x10710f (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10710f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10710f 2 (.base 3 (.d8 0x10)))
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10710f 2 (.base 3 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10710f 0x48 (by decide) 2 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x107113 [0x48, 0x8B, 0x43, 0x18] (LoadPre 0x107113 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x107113 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107113 0 (.base 3 (.d8 0x18)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107113 0 (.base 3 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x107113 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x107117 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x107117) (movR64R64Effect 0x107117 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x107117 1 0).toInstrSpec (mov_r64_r64_effect_step 0x107117 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10711a [0x48, 0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x10711a) (shrR64Effect 0x10711a 4 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10711a 4 1 2).toInstrSpec (shr_r64_imm8_effect_step 0x10711a 0x48 0xe9 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10711e [0x48, 0x89, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00] (StorePre 0x10711e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10711e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10711e 0 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10711e 0 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_m64_r64_effect_step 0x10711e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x107126 [0x83, 0xE0, 0x03] (fun s => s.RIP = 0x107126) (andR32Imm8Effect 0x107126 3 0 0x3)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x107126 3 0 0x3).toInstrSpec (and_r32_imm8_effect_step 0x107126 0xe0 0x3 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x107129 [0x48, 0x89, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00] (StorePre 0x107129 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x107129 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107129 0 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107129 0 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x107129 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x107131 [0x48, 0x89, 0x8C, 0x24, 0x48, 0x01, 0x00, 0x00] (StorePre 0x107131 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x107131 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107131 1 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107131 1 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (mov_m64_r64_effect_step 0x107131 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x107139 [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x107139) (testR64R64Effect 0x107139 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x107139 1 1).toInstrSpec (test_r64_r64_effect_step 0x107139 0x48 0xc9 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10713c [0x4C, 0x89, 0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00] (StorePre 0x10713c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10713c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10713c 9 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10713c 9 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x10713c 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107103) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107107) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10710f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107113) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107117) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 62), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10711a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 60), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10711e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 60), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107126) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107129) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107131) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107139) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 67), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10713c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 67), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107144) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jcc (n := 74) (jcc_rel32_effect_step 0x107144 4 0xf15) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l107100 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107100 :=
  Rest.liftedBlock (rest_l107100 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107100 x hx)

theorem rest_l10714a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10714a bytes_l10714a) (entryMap (live .l10714a))
      3 0x10714a bytes_l10714a b_l10714a := by
  have f0 : InstrSpec 0x10714a [0x48, 0xC7, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10714a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10714a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10714a (.sib 4 none 0 (.d32 0xe0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10714a (.sib 4 none 0 (.d32 0xe0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10714a 0x48 (by decide) (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x107156 [0x48, 0x89, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x107156 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x107156 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107156 2 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107156 2 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x107156 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107156) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10715e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x10715e 0x8a5 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10714a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10714a :=
  Rest.liftedBlock (rest_l10714a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10714a x hx)

theorem rest_l107170_3 [Bindings] (code : CodeMap) :
    Rest (n := 166) code lifted (codeRange 0x107170 bytes_l107170) [(0, 0), (1, 1), (2, 164), (3, 74), (4, 4), (5, 56), (6, 151), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      20 0x10724f bytes_l107170_3 b_l107170_3 := by
  have f60 : InstrSpec 0x10724f [0x48, 0x31, 0xCA] (fun s => s.RIP = 0x10724f) (xorR64R64Effect 0x10724f 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10724f 2 1).toInstrSpec (xor_r64_r64_effect_step 0x10724f 0x48 0xca (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x107252 [0x4C, 0x21, 0xF2] (fun s => s.RIP = 0x107252) (andR64R64Effect 0x107252 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107252 2 14).toInstrSpec (and_r64_r64_effect_step 0x107252 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x107255 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x107255) (movR64R64Effect 0x107255 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x107255 6 2).toInstrSpec (mov_r64_r64_effect_step 0x107255 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x107258 [0x48, 0xC1, 0xE6, 0x08] (fun s => s.RIP = 0x107258) (shlR64Effect 0x107258 4 6 8)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR64Effect_footprint 0x107258 4 6 8).toInstrSpec (shl_r64_imm8_effect_step 0x107258 0x48 0xe6 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x10725c [0x48, 0x01, 0xD6] (fun s => s.RIP = 0x10725c) (addR64R64Effect 0x10725c 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10725c 6 2).toInstrSpec (add_r64_r64_effect_step 0x10725c 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x10725f [0x48, 0x31, 0xCE] (fun s => s.RIP = 0x10725f) (xorR64R64Effect 0x10725f 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10725f 6 1).toInstrSpec (xor_r64_r64_effect_step 0x10725f 0x48 0xce (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x107262 [0x48, 0x89, 0x74, 0x24, 0x38] (StorePre 0x107262 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107262 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107262 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107262 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x107262 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f67 : InstrSpec 0x107267 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x107267) (movR64R64Effect 0x107267 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x107267 1 0).toInstrSpec (mov_r64_r64_effect_step 0x107267 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x10726a [0x48, 0xC1, 0xE9, 0x08] (fun s => s.RIP = 0x10726a) (shrR64Effect 0x10726a 4 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10726a 4 1 8).toInstrSpec (shr_r64_imm8_effect_step 0x10726a 0x48 0xe9 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x10726e [0x48, 0x31, 0xC1] (fun s => s.RIP = 0x10726e) (xorR64R64Effect 0x10726e 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10726e 1 0).toInstrSpec (xor_r64_r64_effect_step 0x10726e 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x107271 [0x4C, 0x21, 0xF1] (fun s => s.RIP = 0x107271) (andR64R64Effect 0x107271 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107271 1 14).toInstrSpec (and_r64_r64_effect_step 0x107271 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x107274 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x107274) (movR64R64Effect 0x107274 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x107274 2 1).toInstrSpec (mov_r64_r64_effect_step 0x107274 0x48 0xca (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x107277 [0x48, 0xC1, 0xE2, 0x08] (fun s => s.RIP = 0x107277) (shlR64Effect 0x107277 4 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR64Effect_footprint 0x107277 4 2 8).toInstrSpec (shl_r64_imm8_effect_step 0x107277 0x48 0xe2 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x10727b [0x48, 0x01, 0xCA] (fun s => s.RIP = 0x10727b) (addR64R64Effect 0x10727b 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10727b 2 1).toInstrSpec (add_r64_r64_effect_step 0x10727b 0x48 0xca (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x10727e [0x48, 0x31, 0xC2] (fun s => s.RIP = 0x10727e) (xorR64R64Effect 0x10727e 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10727e 2 0).toInstrSpec (xor_r64_r64_effect_step 0x10727e 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x107281 [0x48, 0x89, 0x54, 0x24, 0x40] (StorePre 0x107281 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107281 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107281 2 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107281 2 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x107281 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f76 : InstrSpec 0x107286 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107286) (movR32Imm32Effect 0x107286 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x107286 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x107286 0xbe (by decide) 0x8) pre_rip
  have f77 : InstrSpec 0x10728b [0x48, 0x8D, 0x5C, 0x24, 0x08] (fun s => s.RIP = 0x10728b) (leaR64Effect 0x10728b 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x10728b 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10728b 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x107290 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x107290) (movR64R64Effect 0x107290 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x107290 7 3).toInstrSpec (mov_r64_r64_effect_step 0x107290 0x48 0xdf (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x107293 [0xE8, 0xF8, 0x9B, 0xFF, 0xFF] (PushPre 0x107293 5) (callEffect (fun _ => 0x100e90) 0x107298)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107293 0x100e90 0x107298).toInstrSpec (call_rel32_effect_step 0x107293 0xffff9bf8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f60 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 0), (1, 1), (2, 166), (3, 74), (4, 4), (5, 56), (6, 151), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107252) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f61 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 0), (1, 1), (2, 168), (3, 74), (4, 4), (5, 56), (6, 151), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107255) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f62 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 0), (1, 1), (2, 168), (3, 74), (4, 4), (5, 56), (6, 170), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107258) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f63 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 0), (1, 1), (2, 168), (3, 74), (4, 4), (5, 56), (6, 172), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10725c) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f64 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 0), (1, 1), (2, 168), (3, 74), (4, 4), (5, 56), (6, 174), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10725f) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.out (n := 176) f65 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 177) (ρ' := [(0, 0), (1, 1), (2, 168), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107262) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.exec (n := 178) (ρ' := [(0, 0), (1, 1), (2, 168), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107267) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f67 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 0), (1, 179), (2, 168), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10726a) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f68 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 0), (1, 181), (2, 168), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10726e) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f69 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 0), (1, 183), (2, 168), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107271) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f70 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 0), (1, 185), (2, 168), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107274) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f71 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 0), (1, 185), (2, 187), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107277) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f72 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 0), (1, 185), (2, 189), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10727b) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f73 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 0), (1, 185), (2, 191), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10727e) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f74 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 0), (1, 185), (2, 193), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107281) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.exec (n := 195) (ρ' := [(0, 0), (1, 185), (2, 193), (3, 74), (4, 4), (5, 56), (6, 176), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107286) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 196) (RestInside.out (n := 196) f76 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 197) (ρ' := [(0, 0), (1, 185), (2, 193), (3, 74), (4, 4), (5, 56), (6, 196), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10728b) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 198) (RestInside.out (n := 198) f77 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 199) (ρ' := [(0, 0), (1, 185), (2, 193), (3, 198), (4, 4), (5, 56), (6, 196), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107290) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f78 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 0), (1, 185), (2, 193), (3, 198), (4, 4), (5, 56), (6, 196), (7, 200), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107293) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f79 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 0), (1, 185), (2, 193), (3, 198), (4, 202), (5, 56), (6, 196), (7, 200), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e90) f79 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 204) (by decide) (by decide) rfl rfl

theorem rest_l107170_2 [Bindings] (code : CodeMap) :
    Rest (n := 128) code lifted (codeRange 0x107170 bytes_l107170) [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 117), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      40 0x10720a bytes_l107170_2 b_l107170_2 := by
  have f40 : InstrSpec 0x10720a [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x10720a) (movR64R64Effect 0x10720a 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10720a 7 6).toInstrSpec (mov_r64_r64_effect_step 0x10720a 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x10720d [0x48, 0xC1, 0xEF, 0x08] (fun s => s.RIP = 0x10720d) (shrR64Effect 0x10720d 4 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x10720d 4 7 8).toInstrSpec (shr_r64_imm8_effect_step 0x10720d 0x48 0xef 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x107211 [0x48, 0x31, 0xF7] (fun s => s.RIP = 0x107211) (xorR64R64Effect 0x107211 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107211 7 6).toInstrSpec (xor_r64_r64_effect_step 0x107211 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x107214 [0x4C, 0x21, 0xF7] (fun s => s.RIP = 0x107214) (andR64R64Effect 0x107214 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107214 7 14).toInstrSpec (and_r64_r64_effect_step 0x107214 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x107217 [0x49, 0x89, 0xF8] (fun s => s.RIP = 0x107217) (movR64R64Effect 0x107217 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x107217 8 7).toInstrSpec (mov_r64_r64_effect_step 0x107217 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x10721a [0x49, 0xC1, 0xE0, 0x08] (fun s => s.RIP = 0x10721a) (shlR64Effect 0x10721a 4 8 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR64Effect_footprint 0x10721a 4 8 8).toInstrSpec (shl_r64_imm8_effect_step 0x10721a 0x49 0xe0 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x10721e [0x49, 0x01, 0xF8] (fun s => s.RIP = 0x10721e) (addR64R64Effect 0x10721e 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10721e 8 7).toInstrSpec (add_r64_r64_effect_step 0x10721e 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x107221 [0x49, 0x31, 0xF0] (fun s => s.RIP = 0x107221) (xorR64R64Effect 0x107221 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107221 8 6).toInstrSpec (xor_r64_r64_effect_step 0x107221 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x107224 [0x4C, 0x89, 0x44, 0x24, 0x28] (StorePre 0x107224 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107224 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107224 8 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107224 8 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x107224 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x107229 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x107229) (movR64R64Effect 0x107229 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x107229 6 2).toInstrSpec (mov_r64_r64_effect_step 0x107229 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x10722c [0x48, 0xC1, 0xEE, 0x08] (fun s => s.RIP = 0x10722c) (shrR64Effect 0x10722c 4 6 8)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x10722c 4 6 8).toInstrSpec (shr_r64_imm8_effect_step 0x10722c 0x48 0xee 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x107230 [0x48, 0x31, 0xD6] (fun s => s.RIP = 0x107230) (xorR64R64Effect 0x107230 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107230 6 2).toInstrSpec (xor_r64_r64_effect_step 0x107230 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x107233 [0x4C, 0x21, 0xF6] (fun s => s.RIP = 0x107233) (andR64R64Effect 0x107233 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107233 6 14).toInstrSpec (and_r64_r64_effect_step 0x107233 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x107236 [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x107236) (movR64R64Effect 0x107236 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x107236 7 6).toInstrSpec (mov_r64_r64_effect_step 0x107236 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x107239 [0x48, 0xC1, 0xE7, 0x08] (fun s => s.RIP = 0x107239) (shlR64Effect 0x107239 4 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64Effect_footprint 0x107239 4 7 8).toInstrSpec (shl_r64_imm8_effect_step 0x107239 0x48 0xe7 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x10723d [0x48, 0x01, 0xF7] (fun s => s.RIP = 0x10723d) (addR64R64Effect 0x10723d 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10723d 7 6).toInstrSpec (add_r64_r64_effect_step 0x10723d 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x107240 [0x48, 0x31, 0xD7] (fun s => s.RIP = 0x107240) (xorR64R64Effect 0x107240 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107240 7 2).toInstrSpec (xor_r64_r64_effect_step 0x107240 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x107243 [0x48, 0x89, 0x7C, 0x24, 0x30] (StorePre 0x107243 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107243 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107243 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107243 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x107243 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f58 : InstrSpec 0x107248 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x107248) (movR64R64Effect 0x107248 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x107248 2 1).toInstrSpec (mov_r64_r64_effect_step 0x107248 0x48 0xca (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x10724b [0x48, 0xC1, 0xEA, 0x08] (fun s => s.RIP = 0x10724b) (shrR64Effect 0x10724b 4 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10724b 4 2 8).toInstrSpec (shr_r64_imm8_effect_step 0x10724b 0x48 0xea 0x8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f40 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 128), (8, 117), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10720d) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f41 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 130), (8, 117), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107211) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f42 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 132), (8, 117), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107214) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f43 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 134), (8, 117), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107217) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f44 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 134), (8, 136), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10721a) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f45 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 134), (8, 138), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10721e) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f46 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 134), (8, 140), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107221) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f47 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 134), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107224) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.exec (n := 144) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 134), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107229) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f49 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 145), (7, 134), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10722c) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f50 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 147), (7, 134), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107230) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f51 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 149), (7, 134), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107233) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f52 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 151), (7, 134), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107236) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f53 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 151), (7, 153), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107239) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f54 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 151), (7, 155), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10723d) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f55 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 151), (7, 157), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107240) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f56 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 151), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107243) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.exec (n := 161) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 151), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107248) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f58 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 0), (1, 1), (2, 162), (3, 74), (4, 4), (5, 56), (6, 151), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10724b) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f59 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 0), (1, 1), (2, 164), (3, 74), (4, 4), (5, 56), (6, 151), (7, 159), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10724f) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107170_3 code

theorem rest_l107170_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x107170 bytes_l107170) [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 83), (11, 89), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      60 0x1071c4 bytes_l107170_1 b_l107170_1 := by
  have f20 : InstrSpec 0x1071c4 [0x4D, 0x31, 0xCB] (fun s => s.RIP = 0x1071c4) (xorR64R64Effect 0x1071c4 11 9)
      [.gpr 11, .gpr 9] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1071c4 11 9).toInstrSpec (xor_r64_r64_effect_step 0x1071c4 0x4d 0xcb (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x1071c7 [0x4C, 0x89, 0x5C, 0x24, 0x10] (StorePre 0x1071c7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1071c7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1071c7 11 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1071c7 11 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1071c7 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x1071cc [0x4D, 0x89, 0xC1] (fun s => s.RIP = 0x1071cc) (movR64R64Effect 0x1071cc 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x1071cc 9 8).toInstrSpec (mov_r64_r64_effect_step 0x1071cc 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x1071cf [0x49, 0xC1, 0xE9, 0x08] (fun s => s.RIP = 0x1071cf) (shrR64Effect 0x1071cf 4 9 8)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x1071cf 4 9 8).toInstrSpec (shr_r64_imm8_effect_step 0x1071cf 0x49 0xe9 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x1071d3 [0x4D, 0x31, 0xC1] (fun s => s.RIP = 0x1071d3) (xorR64R64Effect 0x1071d3 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1071d3 9 8).toInstrSpec (xor_r64_r64_effect_step 0x1071d3 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x1071d6 [0x4D, 0x21, 0xF1] (fun s => s.RIP = 0x1071d6) (andR64R64Effect 0x1071d6 9 14)
      [.gpr 9, .gpr 14] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1071d6 9 14).toInstrSpec (and_r64_r64_effect_step 0x1071d6 0x4d 0xf1 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x1071d9 [0x4D, 0x89, 0xCA] (fun s => s.RIP = 0x1071d9) (movR64R64Effect 0x1071d9 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1071d9 10 9).toInstrSpec (mov_r64_r64_effect_step 0x1071d9 0x4d 0xca (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x1071dc [0x49, 0xC1, 0xE2, 0x08] (fun s => s.RIP = 0x1071dc) (shlR64Effect 0x1071dc 4 10 8)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR64Effect_footprint 0x1071dc 4 10 8).toInstrSpec (shl_r64_imm8_effect_step 0x1071dc 0x49 0xe2 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x1071e0 [0x4D, 0x01, 0xCA] (fun s => s.RIP = 0x1071e0) (addR64R64Effect 0x1071e0 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1071e0 10 9).toInstrSpec (add_r64_r64_effect_step 0x1071e0 0x4d 0xca (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x1071e3 [0x4D, 0x31, 0xC2] (fun s => s.RIP = 0x1071e3) (xorR64R64Effect 0x1071e3 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1071e3 10 8).toInstrSpec (xor_r64_r64_effect_step 0x1071e3 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x1071e6 [0x4C, 0x89, 0x54, 0x24, 0x18] (StorePre 0x1071e6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1071e6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1071e6 10 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1071e6 10 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1071e6 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x1071eb [0x49, 0x89, 0xF8] (fun s => s.RIP = 0x1071eb) (movR64R64Effect 0x1071eb 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1071eb 8 7).toInstrSpec (mov_r64_r64_effect_step 0x1071eb 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x1071ee [0x49, 0xC1, 0xE8, 0x08] (fun s => s.RIP = 0x1071ee) (shrR64Effect 0x1071ee 4 8 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x1071ee 4 8 8).toInstrSpec (shr_r64_imm8_effect_step 0x1071ee 0x49 0xe8 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x1071f2 [0x49, 0x31, 0xF8] (fun s => s.RIP = 0x1071f2) (xorR64R64Effect 0x1071f2 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1071f2 8 7).toInstrSpec (xor_r64_r64_effect_step 0x1071f2 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x1071f5 [0x4D, 0x21, 0xF0] (fun s => s.RIP = 0x1071f5) (andR64R64Effect 0x1071f5 8 14)
      [.gpr 8, .gpr 14] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1071f5 8 14).toInstrSpec (and_r64_r64_effect_step 0x1071f5 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x1071f8 [0x4D, 0x89, 0xC1] (fun s => s.RIP = 0x1071f8) (movR64R64Effect 0x1071f8 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x1071f8 9 8).toInstrSpec (mov_r64_r64_effect_step 0x1071f8 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x1071fb [0x49, 0xC1, 0xE1, 0x08] (fun s => s.RIP = 0x1071fb) (shlR64Effect 0x1071fb 4 9 8)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR64Effect_footprint 0x1071fb 4 9 8).toInstrSpec (shl_r64_imm8_effect_step 0x1071fb 0x49 0xe1 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x1071ff [0x4D, 0x01, 0xC1] (fun s => s.RIP = 0x1071ff) (addR64R64Effect 0x1071ff 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1071ff 9 8).toInstrSpec (add_r64_r64_effect_step 0x1071ff 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x107202 [0x49, 0x31, 0xF9] (fun s => s.RIP = 0x107202) (xorR64R64Effect 0x107202 9 7)
      [.gpr 9, .gpr 7] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107202 9 7).toInstrSpec (xor_r64_r64_effect_step 0x107202 0x49 0xf9 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x107205 [0x4C, 0x89, 0x4C, 0x24, 0x20] (StorePre 0x107205 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107205 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107205 9 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107205 9 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x107205 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 83), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071c7) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 83), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071cc) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f22 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 94), (10, 83), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071cf) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f23 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 96), (10, 83), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071d3) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f24 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 98), (10, 83), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071d6) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f25 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 100), (10, 83), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071d9) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f26 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 100), (10, 102), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071dc) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f27 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 100), (10, 104), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071e0) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f28 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 100), (10, 106), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071e3) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f29 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 100), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071e6) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.exec (n := 110) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 100), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071eb) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f31 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 111), (9, 100), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071ee) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f32 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 113), (9, 100), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071f2) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f33 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 115), (9, 100), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071f5) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f34 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 117), (9, 100), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071f8) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f35 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 117), (9, 119), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071fb) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 117), (9, 121), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071ff) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 117), (9, 123), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107202) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f38 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 117), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107205) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.exec (n := 127) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 117), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10720a) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107170_2 code

theorem rest_l107170 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107170 bytes_l107170) (entryMap (live .l107170))
      80 0x107170 bytes_l107170 b_l107170 := by
  have f0 : InstrSpec 0x107170 [0x48, 0x8B, 0xAC, 0x24, 0xE0, 0x00, 0x00, 0x00] (LoadPre 0x107170 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x107170 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107170 5 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x107170 5 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_r64_m64_effect_step 0x107170 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107178 [0x48, 0x89, 0xAC, 0x24, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x107178 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x107178 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107178 5 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107178 5 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x107178 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x107180 [0x48, 0xC1, 0xE5, 0x06] (fun s => s.RIP = 0x107180) (shlR64Effect 0x107180 4 5 6)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shlR64Effect_footprint 0x107180 4 5 6).toInstrSpec (shl_r64_imm8_effect_step 0x107180 0x48 0xe5 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x107184 [0x4D, 0x89, 0xD3] (fun s => s.RIP = 0x107184) (movR64R64Effect 0x107184 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x107184 11 10).toInstrSpec (mov_r64_r64_effect_step 0x107184 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x107187 [0x49, 0xC1, 0xEB, 0x08] (fun s => s.RIP = 0x107187) (shrR64Effect 0x107187 4 11 8)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR64Effect_footprint 0x107187 4 11 8).toInstrSpec (shr_r64_imm8_effect_step 0x107187 0x49 0xeb 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10718b [0x4D, 0x31, 0xD3] (fun s => s.RIP = 0x10718b) (xorR64R64Effect 0x10718b 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10718b 11 10).toInstrSpec (xor_r64_r64_effect_step 0x10718b 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10718e [0x49, 0xBE, 0x00, 0x00, 0xFF, 0x00, 0x00, 0x00, 0xFF, 0x00] (fun s => s.RIP = 0x10718e) (movR64Imm64Effect 0x10718e 14 0xff000000ff0000)
      [] [] [.reg 14, .rip] :=
    (movR64Imm64Effect_footprint 0x10718e 14 0xff000000ff0000).toInstrSpec (mov_r64_imm64_effect_step 0x10718e 0x49 0xbe (by decide) (by decide) 0xff000000ff0000) pre_rip
  have f7 : InstrSpec 0x107198 [0x4D, 0x21, 0xF3] (fun s => s.RIP = 0x107198) (andR64R64Effect 0x107198 11 14)
      [.gpr 11, .gpr 14] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107198 11 14).toInstrSpec (and_r64_r64_effect_step 0x107198 0x4d 0xf3 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10719b [0x4C, 0x89, 0xDB] (fun s => s.RIP = 0x10719b) (movR64R64Effect 0x10719b 3 11)
      [.gpr 11] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10719b 3 11).toInstrSpec (mov_r64_r64_effect_step 0x10719b 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10719e [0x48, 0xC1, 0xE3, 0x08] (fun s => s.RIP = 0x10719e) (shlR64Effect 0x10719e 4 3 8)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shlR64Effect_footprint 0x10719e 4 3 8).toInstrSpec (shl_r64_imm8_effect_step 0x10719e 0x48 0xe3 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1071a2 [0x4C, 0x01, 0xDB] (fun s => s.RIP = 0x1071a2) (addR64R64Effect 0x1071a2 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1071a2 3 11).toInstrSpec (add_r64_r64_effect_step 0x1071a2 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1071a5 [0x4C, 0x31, 0xD3] (fun s => s.RIP = 0x1071a5) (xorR64R64Effect 0x1071a5 3 10)
      [.gpr 3, .gpr 10] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1071a5 3 10).toInstrSpec (xor_r64_r64_effect_step 0x1071a5 0x4c 0xd3 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1071a8 [0x48, 0x89, 0x5C, 0x24, 0x08] (StorePre 0x1071a8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1071a8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1071a8 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1071a8 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1071a8 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1071ad [0x4D, 0x89, 0xCA] (fun s => s.RIP = 0x1071ad) (movR64R64Effect 0x1071ad 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1071ad 10 9).toInstrSpec (mov_r64_r64_effect_step 0x1071ad 0x4d 0xca (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1071b0 [0x49, 0xC1, 0xEA, 0x08] (fun s => s.RIP = 0x1071b0) (shrR64Effect 0x1071b0 4 10 8)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR64Effect_footprint 0x1071b0 4 10 8).toInstrSpec (shr_r64_imm8_effect_step 0x1071b0 0x49 0xea 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1071b4 [0x4D, 0x31, 0xCA] (fun s => s.RIP = 0x1071b4) (xorR64R64Effect 0x1071b4 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1071b4 10 9).toInstrSpec (xor_r64_r64_effect_step 0x1071b4 0x4d 0xca (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1071b7 [0x4D, 0x21, 0xF2] (fun s => s.RIP = 0x1071b7) (andR64R64Effect 0x1071b7 10 14)
      [.gpr 10, .gpr 14] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1071b7 10 14).toInstrSpec (and_r64_r64_effect_step 0x1071b7 0x4d 0xf2 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1071ba [0x4D, 0x89, 0xD3] (fun s => s.RIP = 0x1071ba) (movR64R64Effect 0x1071ba 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x1071ba 11 10).toInstrSpec (mov_r64_r64_effect_step 0x1071ba 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1071bd [0x49, 0xC1, 0xE3, 0x08] (fun s => s.RIP = 0x1071bd) (shlR64Effect 0x1071bd 4 11 8)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR64Effect_footprint 0x1071bd 4 11 8).toInstrSpec (shl_r64_imm8_effect_step 0x1071bd 0x49 0xe3 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1071c1 [0x4D, 0x01, 0xD3] (fun s => s.RIP = 0x1071c1) (addR64R64Effect 0x1071c1 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1071c1 11 10).toInstrSpec (add_r64_r64_effect_step 0x1071c1 0x4d 0xd3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107178) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107180) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107184) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 58), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107187) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10718b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 62), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10718e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 62), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107198) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10719b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10719e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 70), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071a2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 72), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071a5) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071a8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071ad) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 77), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071b0) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 79), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071b4) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 81), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071b7) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 83), (11, 66), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071ba) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 83), (11, 85), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071bd) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 83), (11, 87), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071c1) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 83), (11, 89), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071c4) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107170_1 code

theorem block_l107170 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107170 :=
  Rest.liftedBlock (rest_l107170 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107170 x hx)

theorem rest_l107298 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107298 bytes_l107298) (entryMap (live .l107298))
      20 0x107298 bytes_l107298 b_l107298 := by
  have f0 : InstrSpec 0x107298 [0x48, 0x8B, 0x84, 0x24, 0xD8, 0x03, 0x00, 0x00] (LoadPre 0x107298 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3d8)) s (0x107298 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107298 0 (.sib 4 none 0 (.d32 0x3d8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107298 0 (.sib 4 none 0 (.d32 0x3d8))).toInstrSpec (mov_r64_m64_effect_step 0x107298 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x3d8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1072a0 [0x48, 0x31, 0x44, 0x24, 0x08] (StorePre 0x1072a0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1072a0 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x1072a0 5 64 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x1072a0 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (xor_m64_r64_effect_step 0x1072a0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1072a5 [0x48, 0x8B, 0x84, 0x24, 0xE0, 0x03, 0x00, 0x00] (LoadPre 0x1072a5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3e0)) s (0x1072a5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1072a5 0 (.sib 4 none 0 (.d32 0x3e0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1072a5 0 (.sib 4 none 0 (.d32 0x3e0))).toInstrSpec (mov_r64_m64_effect_step 0x1072a5 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x3e0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1072ad [0x48, 0x31, 0x44, 0x24, 0x10] (StorePre 0x1072ad 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1072ad + BitVec.ofNat 64 5)) 8) (xorMREffect 0x1072ad 5 64 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x1072ad 5 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (xor_m64_r64_effect_step 0x1072ad 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1072b2 [0x48, 0x8B, 0x84, 0x24, 0xE8, 0x03, 0x00, 0x00] (LoadPre 0x1072b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3e8)) s (0x1072b2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1072b2 0 (.sib 4 none 0 (.d32 0x3e8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1072b2 0 (.sib 4 none 0 (.d32 0x3e8))).toInstrSpec (mov_r64_m64_effect_step 0x1072b2 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x3e8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1072ba [0x48, 0x31, 0x44, 0x24, 0x18] (StorePre 0x1072ba 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1072ba + BitVec.ofNat 64 5)) 8) (xorMREffect 0x1072ba 5 64 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x1072ba 5 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (xor_m64_r64_effect_step 0x1072ba 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1072bf [0x48, 0x8B, 0x84, 0x24, 0xF0, 0x03, 0x00, 0x00] (LoadPre 0x1072bf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3f0)) s (0x1072bf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1072bf 0 (.sib 4 none 0 (.d32 0x3f0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1072bf 0 (.sib 4 none 0 (.d32 0x3f0))).toInstrSpec (mov_r64_m64_effect_step 0x1072bf 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x3f0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1072c7 [0x48, 0x31, 0x44, 0x24, 0x20] (StorePre 0x1072c7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1072c7 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x1072c7 5 64 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x1072c7 5 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (xor_m64_r64_effect_step 0x1072c7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1072cc [0x48, 0x8B, 0x84, 0x24, 0xF8, 0x03, 0x00, 0x00] (LoadPre 0x1072cc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3f8)) s (0x1072cc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1072cc 0 (.sib 4 none 0 (.d32 0x3f8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1072cc 0 (.sib 4 none 0 (.d32 0x3f8))).toInstrSpec (mov_r64_m64_effect_step 0x1072cc 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x3f8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1072d4 [0x48, 0x31, 0x44, 0x24, 0x28] (StorePre 0x1072d4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1072d4 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x1072d4 5 64 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x1072d4 5 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (xor_m64_r64_effect_step 0x1072d4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1072d9 [0x48, 0x8B, 0x84, 0x24, 0x00, 0x04, 0x00, 0x00] (LoadPre 0x1072d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x400)) s (0x1072d9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1072d9 0 (.sib 4 none 0 (.d32 0x400)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1072d9 0 (.sib 4 none 0 (.d32 0x400))).toInstrSpec (mov_r64_m64_effect_step 0x1072d9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x400)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1072e1 [0x48, 0x31, 0x44, 0x24, 0x30] (StorePre 0x1072e1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1072e1 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x1072e1 5 64 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x1072e1 5 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (xor_m64_r64_effect_step 0x1072e1 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1072e6 [0x48, 0x8B, 0x84, 0x24, 0x08, 0x04, 0x00, 0x00] (LoadPre 0x1072e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x408)) s (0x1072e6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1072e6 0 (.sib 4 none 0 (.d32 0x408)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1072e6 0 (.sib 4 none 0 (.d32 0x408))).toInstrSpec (mov_r64_m64_effect_step 0x1072e6 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x408)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1072ee [0x48, 0x31, 0x44, 0x24, 0x38] (StorePre 0x1072ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1072ee + BitVec.ofNat 64 5)) 8) (xorMREffect 0x1072ee 5 64 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x1072ee 5 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (xor_m64_r64_effect_step 0x1072ee 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1072f3 [0x48, 0x8B, 0x84, 0x24, 0x10, 0x04, 0x00, 0x00] (LoadPre 0x1072f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x410)) s (0x1072f3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1072f3 0 (.sib 4 none 0 (.d32 0x410)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1072f3 0 (.sib 4 none 0 (.d32 0x410))).toInstrSpec (mov_r64_m64_effect_step 0x1072f3 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x410)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1072fb [0x48, 0x31, 0x44, 0x24, 0x40] (StorePre 0x1072fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1072fb + BitVec.ofNat 64 5)) 8) (xorMREffect 0x1072fb 5 64 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x1072fb 5 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (xor_m64_r64_effect_step 0x1072fb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x107300 [0xBA, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107300) (movR32Imm32Effect 0x107300 5 2 0x8)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x107300 5 2 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x107300 0xba (by decide) 0x8) pre_rip
  have f17 : InstrSpec 0x107305 [0x48, 0x8D, 0xBC, 0x24, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107305) (leaR64Effect 0x107305 7 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x107305 7 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (lea_r64_effect_step 0x107305 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10730d [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x10730d) (movR64R64Effect 0x10730d 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10730d 6 3).toInstrSpec (mov_r64_r64_effect_step 0x10730d 0x48 0xde (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x107310 [0xE8, 0xFB, 0x2E, 0x00, 0x00] (PushPre 0x107310 5) (callEffect (fun _ => 0x10a210) 0x107315)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107310 0x10a210 0x107315).toInstrSpec (call_rel32_effect_step 0x107310 0x2efb (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072a0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072a5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072ad) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072b2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072ba) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072bf) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072c7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072cc) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072d4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072d9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072e1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072e6) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072ee) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072f3) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072fb) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107300) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 74), (2, 77), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107305) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 74), (2, 77), (3, 3), (4, 4), (5, 5), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10730d) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 74), (2, 77), (3, 3), (4, 4), (5, 5), (6, 81), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107310) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 74), (2, 77), (3, 3), (4, 83), (5, 5), (6, 81), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a210) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem block_l107298 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107298 :=
  Rest.liftedBlock (rest_l107298 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107298 x hx)

theorem rest_l107315_15 [Bindings] (code : CodeMap) :
    Rest (n := 539) code lifted (codeRange 0x107315 bytes_l107315) [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]
      13 0x1079c0 bytes_l107315_15 b_l107315_15 := by
  have f300 : InstrSpec 0x1079c0 [0x44, 0x88, 0x4C, 0x28, 0x3A] (StorePre 0x1079c0 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3a)) s (0x1079c0 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079c0 5 9 (.sib 0 (some 5) 0 (.d8 0x3a)))
      [.gpr 9, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1079c0 5 9 (.sib 0 (some 5) 0 (.d8 0x3a))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1079c0 0x44 (by decide) 1 (.sib 0 (some 5) 0 (.d8 0x3a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f301 : InstrSpec 0x1079c5 [0x44, 0x88, 0x44, 0x28, 0x3B] (StorePre 0x1079c5 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3b)) s (0x1079c5 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079c5 5 8 (.sib 0 (some 5) 0 (.d8 0x3b)))
      [.gpr 8, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1079c5 5 8 (.sib 0 (some 5) 0 (.d8 0x3b))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1079c5 0x44 (by decide) 0 (.sib 0 (some 5) 0 (.d8 0x3b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f302 : InstrSpec 0x1079ca [0x40, 0x88, 0x7C, 0x28, 0x3C] (StorePre 0x1079ca 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3c)) s (0x1079ca + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079ca 5 7 (.sib 0 (some 5) 0 (.d8 0x3c)))
      [.gpr 7, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1079ca 5 7 (.sib 0 (some 5) 0 (.d8 0x3c))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1079ca 0x40 (by decide) 7 (.sib 0 (some 5) 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f303 : InstrSpec 0x1079cf [0x40, 0x88, 0x74, 0x28, 0x3D] (StorePre 0x1079cf 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3d)) s (0x1079cf + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079cf 5 6 (.sib 0 (some 5) 0 (.d8 0x3d)))
      [.gpr 6, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1079cf 5 6 (.sib 0 (some 5) 0 (.d8 0x3d))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1079cf 0x40 (by decide) 6 (.sib 0 (some 5) 0 (.d8 0x3d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f304 : InstrSpec 0x1079d4 [0x88, 0x54, 0x28, 0x3E] (StorePre 0x1079d4 4 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3e)) s (0x1079d4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1079d4 4 2 (.sib 0 (some 5) 0 (.d8 0x3e)))
      [.gpr 2, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1079d4 4 2 (.sib 0 (some 5) 0 (.d8 0x3e))).toInstrSpec (mov_m8_r8_effect_step 0x1079d4 2 (by decide) (.sib 0 (some 5) 0 (.d8 0x3e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f305 : InstrSpec 0x1079d8 [0x48, 0x89, 0xC2] (fun s => s.RIP = 0x1079d8) (movR64R64Effect 0x1079d8 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1079d8 2 0).toInstrSpec (mov_r64_r64_effect_step 0x1079d8 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f306 : InstrSpec 0x1079db [0x88, 0x4C, 0x28, 0x3F] (StorePre 0x1079db 4 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3f)) s (0x1079db + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1079db 4 1 (.sib 0 (some 5) 0 (.d8 0x3f)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1079db 4 1 (.sib 0 (some 5) 0 (.d8 0x3f))).toInstrSpec (mov_m8_r8_effect_step 0x1079db 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x3f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f307 : InstrSpec 0x1079df [0x48, 0x8B, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00] (LoadPre 0x1079df (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1079df + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1079df 1 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1079df 1 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_r64_m64_effect_step 0x1079df 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f308 : InstrSpec 0x1079e7 [0x48, 0xFF, 0xC1] (fun s => s.RIP = 0x1079e7) (incR64Effect 0x1079e7 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (incR64Effect_footprint 0x1079e7 1).toInstrSpec (inc_r64_effect_step 0x1079e7 0x48 0xc1 (by decide) (by decide) (by decide)) pre_rip
  have f309 : InstrSpec 0x1079ea [0x48, 0x89, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x1079ea 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1079ea + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1079ea 1 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1079ea 1 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x1079ea 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f310 : InstrSpec 0x1079f2 [0x48, 0x39, 0x8C, 0x24, 0x48, 0x01, 0x00, 0x00] (LoadPre 0x1079f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x1079f2 + BitVec.ofNat 64 8)) 8) (cmpMREffect 0x1079f2 8 64 1 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 1, .gpr 4] [] [.flags, .rip] :=
    (cmpMREffect64_footprint 0x1079f2 8 1 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (cmp_m64_r64_effect_step 0x1079f2 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f311 : InstrSpec 0x1079fa [0x4C, 0x8B, 0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00] (LoadPre 0x1079fa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x1079fa + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1079fa 9 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1079fa 9 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_r64_m64_effect_step 0x1079fa 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 539) (RestInside.exec (n := 539) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079c5) f300 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 540) (RestInside.exec (n := 540) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079ca) f301 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 541) (RestInside.exec (n := 541) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079cf) f302 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 542) (RestInside.exec (n := 542) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079d4) f303 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 543) (RestInside.exec (n := 543) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079d8) f304 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 544) (RestInside.out (n := 544) f305 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 545) (ρ' := [(0, 375), (1, 373), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079db) f305 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 546) (RestInside.exec (n := 546) (ρ' := [(0, 375), (1, 373), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079df) f306 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 547) (RestInside.out (n := 547) f307 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 548) (ρ' := [(0, 375), (1, 547), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079e7) f307 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 549) (RestInside.out (n := 549) f308 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 550) (ρ' := [(0, 375), (1, 549), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079ea) f308 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 551) (RestInside.exec (n := 551) (ρ' := [(0, 375), (1, 549), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079f2) f309 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 552) (RestInside.out (n := 552) f310 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 553) (ρ' := [(0, 375), (1, 549), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (19, 552), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079fa) f310 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 554) (RestInside.out (n := 554) f311 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 555) (ρ' := [(0, 375), (1, 549), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 554), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (19, 552), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a02) f311 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 556) (jcc_rel32_effect_step 0x107a02 4 0x657) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l107315_14 [Bindings] (code : CodeMap) :
    Rest (n := 512) code lifted (codeRange 0x107315 bytes_l107315) [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 509), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]
      33 0x107956 bytes_l107315_14 b_l107315_14 := by
  have f280 : InstrSpec 0x107956 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4E] (LoadPre 0x107956 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4e)) s (0x107956 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107956 6 13 (.sib 4 none 0 (.d8 0x4e)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107956 6 13 (.sib 4 none 0 (.d8 0x4e))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107956 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x4e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f281 : InstrSpec 0x10795c [0x44, 0x88, 0x6C, 0x28, 0x2D] (StorePre 0x10795c 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2d)) s (0x10795c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10795c 5 13 (.sib 0 (some 5) 0 (.d8 0x2d)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x10795c 5 13 (.sib 0 (some 5) 0 (.d8 0x2d))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10795c 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f282 : InstrSpec 0x107961 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4D] (LoadPre 0x107961 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x107961 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107961 6 13 (.sib 4 none 0 (.d8 0x4d)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107961 6 13 (.sib 4 none 0 (.d8 0x4d))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107961 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x4d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f283 : InstrSpec 0x107967 [0x44, 0x88, 0x6C, 0x28, 0x2E] (StorePre 0x107967 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2e)) s (0x107967 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107967 5 13 (.sib 0 (some 5) 0 (.d8 0x2e)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107967 5 13 (.sib 0 (some 5) 0 (.d8 0x2e))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107967 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x2e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f284 : InstrSpec 0x10796c [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4C] (LoadPre 0x10796c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x10796c + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10796c 6 13 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x10796c 6 13 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10796c 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f285 : InstrSpec 0x107972 [0x44, 0x88, 0x6C, 0x28, 0x2F] (StorePre 0x107972 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2f)) s (0x107972 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107972 5 13 (.sib 0 (some 5) 0 (.d8 0x2f)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107972 5 13 (.sib 0 (some 5) 0 (.d8 0x2f))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107972 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x2f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f286 : InstrSpec 0x107977 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4B] (LoadPre 0x107977 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x107977 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107977 6 13 (.sib 4 none 0 (.d8 0x4b)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107977 6 13 (.sib 4 none 0 (.d8 0x4b))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107977 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x4b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f287 : InstrSpec 0x10797d [0x44, 0x88, 0x6C, 0x28, 0x30] (StorePre 0x10797d 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x30)) s (0x10797d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10797d 5 13 (.sib 0 (some 5) 0 (.d8 0x30)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x10797d 5 13 (.sib 0 (some 5) 0 (.d8 0x30))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10797d 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f288 : InstrSpec 0x107982 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4A] (LoadPre 0x107982 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x107982 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107982 6 13 (.sib 4 none 0 (.d8 0x4a)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107982 6 13 (.sib 4 none 0 (.d8 0x4a))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107982 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x4a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f289 : InstrSpec 0x107988 [0x44, 0x88, 0x6C, 0x28, 0x31] (StorePre 0x107988 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x31)) s (0x107988 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107988 5 13 (.sib 0 (some 5) 0 (.d8 0x31)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107988 5 13 (.sib 0 (some 5) 0 (.d8 0x31))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107988 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x31)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f290 : InstrSpec 0x10798d [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x49] (LoadPre 0x10798d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x49)) s (0x10798d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10798d 6 13 (.sib 4 none 0 (.d8 0x49)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x10798d 6 13 (.sib 4 none 0 (.d8 0x49))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10798d 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x49)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f291 : InstrSpec 0x107993 [0x44, 0x88, 0x6C, 0x28, 0x32] (StorePre 0x107993 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x32)) s (0x107993 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107993 5 13 (.sib 0 (some 5) 0 (.d8 0x32)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107993 5 13 (.sib 0 (some 5) 0 (.d8 0x32))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107993 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x32)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f292 : InstrSpec 0x107998 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x48] (LoadPre 0x107998 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x107998 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107998 6 13 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107998 6 13 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107998 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f293 : InstrSpec 0x10799e [0x44, 0x88, 0x6C, 0x28, 0x33] (StorePre 0x10799e 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x33)) s (0x10799e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10799e 5 13 (.sib 0 (some 5) 0 (.d8 0x33)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x10799e 5 13 (.sib 0 (some 5) 0 (.d8 0x33))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10799e 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x33)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f294 : InstrSpec 0x1079a3 [0x44, 0x88, 0x64, 0x28, 0x34] (StorePre 0x1079a3 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x34)) s (0x1079a3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079a3 5 12 (.sib 0 (some 5) 0 (.d8 0x34)))
      [.gpr 12, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1079a3 5 12 (.sib 0 (some 5) 0 (.d8 0x34))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1079a3 0x44 (by decide) 4 (.sib 0 (some 5) 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f295 : InstrSpec 0x1079a8 [0x44, 0x88, 0x7C, 0x28, 0x35] (StorePre 0x1079a8 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x35)) s (0x1079a8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079a8 5 15 (.sib 0 (some 5) 0 (.d8 0x35)))
      [.gpr 15, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1079a8 5 15 (.sib 0 (some 5) 0 (.d8 0x35))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1079a8 0x44 (by decide) 7 (.sib 0 (some 5) 0 (.d8 0x35)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f296 : InstrSpec 0x1079ad [0x44, 0x88, 0x74, 0x28, 0x36] (StorePre 0x1079ad 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x36)) s (0x1079ad + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079ad 5 14 (.sib 0 (some 5) 0 (.d8 0x36)))
      [.gpr 14, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1079ad 5 14 (.sib 0 (some 5) 0 (.d8 0x36))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1079ad 0x44 (by decide) 6 (.sib 0 (some 5) 0 (.d8 0x36)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f297 : InstrSpec 0x1079b2 [0x88, 0x5C, 0x28, 0x37] (StorePre 0x1079b2 4 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x37)) s (0x1079b2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1079b2 4 3 (.sib 0 (some 5) 0 (.d8 0x37)))
      [.gpr 3, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1079b2 4 3 (.sib 0 (some 5) 0 (.d8 0x37))).toInstrSpec (mov_m8_r8_effect_step 0x1079b2 3 (by decide) (.sib 0 (some 5) 0 (.d8 0x37)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f298 : InstrSpec 0x1079b6 [0x44, 0x88, 0x5C, 0x28, 0x38] (StorePre 0x1079b6 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x38)) s (0x1079b6 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079b6 5 11 (.sib 0 (some 5) 0 (.d8 0x38)))
      [.gpr 11, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1079b6 5 11 (.sib 0 (some 5) 0 (.d8 0x38))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1079b6 0x44 (by decide) 3 (.sib 0 (some 5) 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f299 : InstrSpec 0x1079bb [0x44, 0x88, 0x54, 0x28, 0x39] (StorePre 0x1079bb 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x39)) s (0x1079bb + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079bb 5 10 (.sib 0 (some 5) 0 (.d8 0x39)))
      [.gpr 10, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1079bb 5 10 (.sib 0 (some 5) 0 (.d8 0x39))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1079bb 0x44 (by decide) 2 (.sib 0 (some 5) 0 (.d8 0x39)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 512) (RestInside.out (n := 512) f280 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 513) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 512), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10795c) f280 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 514) (RestInside.exec (n := 514) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 512), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107961) f281 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 515) (RestInside.out (n := 515) f282 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 516) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 515), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107967) f282 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 517) (RestInside.exec (n := 517) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 515), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10796c) f283 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 518) (RestInside.out (n := 518) f284 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 519) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 518), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107972) f284 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 520) (RestInside.exec (n := 520) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 518), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107977) f285 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 521) (RestInside.out (n := 521) f286 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 522) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 521), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10797d) f286 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 523) (RestInside.exec (n := 523) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 521), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107982) f287 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 524) (RestInside.out (n := 524) f288 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 525) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 524), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107988) f288 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 526) (RestInside.exec (n := 526) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 524), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10798d) f289 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 527) (RestInside.out (n := 527) f290 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 528) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 527), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107993) f290 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 529) (RestInside.exec (n := 529) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 527), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107998) f291 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 530) (RestInside.out (n := 530) f292 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 531) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10799e) f292 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 532) (RestInside.exec (n := 532) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079a3) f293 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 533) (RestInside.exec (n := 533) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079a8) f294 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 534) (RestInside.exec (n := 534) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079ad) f295 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 535) (RestInside.exec (n := 535) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079b2) f296 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 536) (RestInside.exec (n := 536) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079b6) f297 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 537) (RestInside.exec (n := 537) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079bb) f298 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 538) (RestInside.exec (n := 538) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1079c0) f299 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107315_15 code

theorem rest_l107315_13 [Bindings] (code : CodeMap) :
    Rest (n := 482) code lifted (codeRange 0x107315 bytes_l107315) [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 479), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]
      53 0x1078e8 bytes_l107315_13 b_l107315_13 := by
  have f260 : InstrSpec 0x1078e8 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x58] (LoadPre 0x1078e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1078e8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078e8 6 13 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1078e8 6 13 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1078e8 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f261 : InstrSpec 0x1078ee [0x44, 0x88, 0x6C, 0x28, 0x23] (StorePre 0x1078ee 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x23)) s (0x1078ee + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078ee 5 13 (.sib 0 (some 5) 0 (.d8 0x23)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1078ee 5 13 (.sib 0 (some 5) 0 (.d8 0x23))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1078ee 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x23)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f262 : InstrSpec 0x1078f3 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x57] (LoadPre 0x1078f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x57)) s (0x1078f3 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078f3 6 13 (.sib 4 none 0 (.d8 0x57)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1078f3 6 13 (.sib 4 none 0 (.d8 0x57))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1078f3 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x57)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f263 : InstrSpec 0x1078f9 [0x44, 0x88, 0x6C, 0x28, 0x24] (StorePre 0x1078f9 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x24)) s (0x1078f9 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078f9 5 13 (.sib 0 (some 5) 0 (.d8 0x24)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1078f9 5 13 (.sib 0 (some 5) 0 (.d8 0x24))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1078f9 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f264 : InstrSpec 0x1078fe [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x56] (LoadPre 0x1078fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x56)) s (0x1078fe + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078fe 6 13 (.sib 4 none 0 (.d8 0x56)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1078fe 6 13 (.sib 4 none 0 (.d8 0x56))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1078fe 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x56)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f265 : InstrSpec 0x107904 [0x44, 0x88, 0x6C, 0x28, 0x25] (StorePre 0x107904 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x25)) s (0x107904 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107904 5 13 (.sib 0 (some 5) 0 (.d8 0x25)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107904 5 13 (.sib 0 (some 5) 0 (.d8 0x25))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107904 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f266 : InstrSpec 0x107909 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x55] (LoadPre 0x107909 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x55)) s (0x107909 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107909 6 13 (.sib 4 none 0 (.d8 0x55)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107909 6 13 (.sib 4 none 0 (.d8 0x55))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107909 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x55)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f267 : InstrSpec 0x10790f [0x44, 0x88, 0x6C, 0x28, 0x26] (StorePre 0x10790f 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x26)) s (0x10790f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10790f 5 13 (.sib 0 (some 5) 0 (.d8 0x26)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x10790f 5 13 (.sib 0 (some 5) 0 (.d8 0x26))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10790f 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x26)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f268 : InstrSpec 0x107914 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x54] (LoadPre 0x107914 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x107914 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107914 6 13 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107914 6 13 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107914 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f269 : InstrSpec 0x10791a [0x44, 0x88, 0x6C, 0x28, 0x27] (StorePre 0x10791a 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x27)) s (0x10791a + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10791a 5 13 (.sib 0 (some 5) 0 (.d8 0x27)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x10791a 5 13 (.sib 0 (some 5) 0 (.d8 0x27))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10791a 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x27)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f270 : InstrSpec 0x10791f [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x53] (LoadPre 0x10791f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x10791f + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10791f 6 13 (.sib 4 none 0 (.d8 0x53)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x10791f 6 13 (.sib 4 none 0 (.d8 0x53))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10791f 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x53)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f271 : InstrSpec 0x107925 [0x44, 0x88, 0x6C, 0x28, 0x28] (StorePre 0x107925 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x28)) s (0x107925 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107925 5 13 (.sib 0 (some 5) 0 (.d8 0x28)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107925 5 13 (.sib 0 (some 5) 0 (.d8 0x28))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107925 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f272 : InstrSpec 0x10792a [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x52] (LoadPre 0x10792a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x52)) s (0x10792a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10792a 6 13 (.sib 4 none 0 (.d8 0x52)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x10792a 6 13 (.sib 4 none 0 (.d8 0x52))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10792a 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x52)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f273 : InstrSpec 0x107930 [0x44, 0x88, 0x6C, 0x28, 0x29] (StorePre 0x107930 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x29)) s (0x107930 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107930 5 13 (.sib 0 (some 5) 0 (.d8 0x29)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107930 5 13 (.sib 0 (some 5) 0 (.d8 0x29))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107930 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x29)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f274 : InstrSpec 0x107935 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x51] (LoadPre 0x107935 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x51)) s (0x107935 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107935 6 13 (.sib 4 none 0 (.d8 0x51)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107935 6 13 (.sib 4 none 0 (.d8 0x51))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107935 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x51)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f275 : InstrSpec 0x10793b [0x44, 0x88, 0x6C, 0x28, 0x2A] (StorePre 0x10793b 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2a)) s (0x10793b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10793b 5 13 (.sib 0 (some 5) 0 (.d8 0x2a)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x10793b 5 13 (.sib 0 (some 5) 0 (.d8 0x2a))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10793b 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x2a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f276 : InstrSpec 0x107940 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x50] (LoadPre 0x107940 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x107940 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107940 6 13 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107940 6 13 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107940 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f277 : InstrSpec 0x107946 [0x44, 0x88, 0x6C, 0x28, 0x2B] (StorePre 0x107946 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2b)) s (0x107946 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107946 5 13 (.sib 0 (some 5) 0 (.d8 0x2b)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107946 5 13 (.sib 0 (some 5) 0 (.d8 0x2b))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107946 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x2b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f278 : InstrSpec 0x10794b [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4F] (LoadPre 0x10794b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x10794b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10794b 6 13 (.sib 4 none 0 (.d8 0x4f)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x10794b 6 13 (.sib 4 none 0 (.d8 0x4f))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10794b 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x4f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f279 : InstrSpec 0x107951 [0x44, 0x88, 0x6C, 0x28, 0x2C] (StorePre 0x107951 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2c)) s (0x107951 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107951 5 13 (.sib 0 (some 5) 0 (.d8 0x2c)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107951 5 13 (.sib 0 (some 5) 0 (.d8 0x2c))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107951 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 482) (RestInside.out (n := 482) f260 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 483) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 482), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078ee) f260 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 484) (RestInside.exec (n := 484) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 482), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078f3) f261 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 485) (RestInside.out (n := 485) f262 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 486) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 485), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078f9) f262 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 487) (RestInside.exec (n := 487) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 485), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078fe) f263 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 488) (RestInside.out (n := 488) f264 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 489) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 488), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107904) f264 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 490) (RestInside.exec (n := 490) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 488), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107909) f265 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 491) (RestInside.out (n := 491) f266 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 492) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 491), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10790f) f266 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 493) (RestInside.exec (n := 493) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 491), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107914) f267 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 494) (RestInside.out (n := 494) f268 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 495) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 494), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10791a) f268 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 496) (RestInside.exec (n := 496) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 494), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10791f) f269 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 497) (RestInside.out (n := 497) f270 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 498) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 497), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107925) f270 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 499) (RestInside.exec (n := 499) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 497), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10792a) f271 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 500) (RestInside.out (n := 500) f272 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 501) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 500), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107930) f272 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 502) (RestInside.exec (n := 502) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 500), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107935) f273 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 503) (RestInside.out (n := 503) f274 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 504) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 503), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10793b) f274 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 505) (RestInside.exec (n := 505) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 503), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107940) f275 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 506) (RestInside.out (n := 506) f276 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 507) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 506), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107946) f276 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 508) (RestInside.exec (n := 508) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 506), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10794b) f277 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 509) (RestInside.out (n := 509) f278 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 510) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 509), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107951) f278 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 511) (RestInside.exec (n := 511) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 509), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107956) f279 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107315_14 code

theorem rest_l107315_12 [Bindings] (code : CodeMap) :
    Rest (n := 452) code lifted (codeRange 0x107315 bytes_l107315) [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 449), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]
      73 0x10787a bytes_l107315_12 b_l107315_12 := by
  have f240 : InstrSpec 0x10787a [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x62] (LoadPre 0x10787a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x10787a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10787a 6 13 (.sib 4 none 0 (.d8 0x62)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x10787a 6 13 (.sib 4 none 0 (.d8 0x62))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10787a 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x62)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f241 : InstrSpec 0x107880 [0x44, 0x88, 0x6C, 0x28, 0x19] (StorePre 0x107880 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x19)) s (0x107880 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107880 5 13 (.sib 0 (some 5) 0 (.d8 0x19)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107880 5 13 (.sib 0 (some 5) 0 (.d8 0x19))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107880 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f242 : InstrSpec 0x107885 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x61] (LoadPre 0x107885 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x61)) s (0x107885 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107885 6 13 (.sib 4 none 0 (.d8 0x61)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107885 6 13 (.sib 4 none 0 (.d8 0x61))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107885 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x61)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f243 : InstrSpec 0x10788b [0x44, 0x88, 0x6C, 0x28, 0x1A] (StorePre 0x10788b 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1a)) s (0x10788b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10788b 5 13 (.sib 0 (some 5) 0 (.d8 0x1a)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x10788b 5 13 (.sib 0 (some 5) 0 (.d8 0x1a))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10788b 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f244 : InstrSpec 0x107890 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x60] (LoadPre 0x107890 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x107890 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107890 6 13 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107890 6 13 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107890 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f245 : InstrSpec 0x107896 [0x44, 0x88, 0x6C, 0x28, 0x1B] (StorePre 0x107896 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1b)) s (0x107896 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107896 5 13 (.sib 0 (some 5) 0 (.d8 0x1b)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107896 5 13 (.sib 0 (some 5) 0 (.d8 0x1b))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107896 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f246 : InstrSpec 0x10789b [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5F] (LoadPre 0x10789b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5f)) s (0x10789b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10789b 6 13 (.sib 4 none 0 (.d8 0x5f)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x10789b 6 13 (.sib 4 none 0 (.d8 0x5f))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10789b 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x5f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f247 : InstrSpec 0x1078a1 [0x44, 0x88, 0x6C, 0x28, 0x1C] (StorePre 0x1078a1 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1c)) s (0x1078a1 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078a1 5 13 (.sib 0 (some 5) 0 (.d8 0x1c)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1078a1 5 13 (.sib 0 (some 5) 0 (.d8 0x1c))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1078a1 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f248 : InstrSpec 0x1078a6 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5E] (LoadPre 0x1078a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x1078a6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078a6 6 13 (.sib 4 none 0 (.d8 0x5e)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1078a6 6 13 (.sib 4 none 0 (.d8 0x5e))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1078a6 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x5e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f249 : InstrSpec 0x1078ac [0x44, 0x88, 0x6C, 0x28, 0x1D] (StorePre 0x1078ac 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1d)) s (0x1078ac + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078ac 5 13 (.sib 0 (some 5) 0 (.d8 0x1d)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1078ac 5 13 (.sib 0 (some 5) 0 (.d8 0x1d))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1078ac 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f250 : InstrSpec 0x1078b1 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5D] (LoadPre 0x1078b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5d)) s (0x1078b1 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078b1 6 13 (.sib 4 none 0 (.d8 0x5d)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1078b1 6 13 (.sib 4 none 0 (.d8 0x5d))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1078b1 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x5d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f251 : InstrSpec 0x1078b7 [0x44, 0x88, 0x6C, 0x28, 0x1E] (StorePre 0x1078b7 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1e)) s (0x1078b7 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078b7 5 13 (.sib 0 (some 5) 0 (.d8 0x1e)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1078b7 5 13 (.sib 0 (some 5) 0 (.d8 0x1e))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1078b7 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f252 : InstrSpec 0x1078bc [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5C] (LoadPre 0x1078bc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x1078bc + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078bc 6 13 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1078bc 6 13 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1078bc 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f253 : InstrSpec 0x1078c2 [0x44, 0x88, 0x6C, 0x28, 0x1F] (StorePre 0x1078c2 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1f)) s (0x1078c2 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078c2 5 13 (.sib 0 (some 5) 0 (.d8 0x1f)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1078c2 5 13 (.sib 0 (some 5) 0 (.d8 0x1f))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1078c2 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f254 : InstrSpec 0x1078c7 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5B] (LoadPre 0x1078c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5b)) s (0x1078c7 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078c7 6 13 (.sib 4 none 0 (.d8 0x5b)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1078c7 6 13 (.sib 4 none 0 (.d8 0x5b))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1078c7 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x5b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f255 : InstrSpec 0x1078cd [0x44, 0x88, 0x6C, 0x28, 0x20] (StorePre 0x1078cd 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x20)) s (0x1078cd + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078cd 5 13 (.sib 0 (some 5) 0 (.d8 0x20)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1078cd 5 13 (.sib 0 (some 5) 0 (.d8 0x20))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1078cd 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f256 : InstrSpec 0x1078d2 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5A] (LoadPre 0x1078d2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5a)) s (0x1078d2 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078d2 6 13 (.sib 4 none 0 (.d8 0x5a)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1078d2 6 13 (.sib 4 none 0 (.d8 0x5a))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1078d2 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x5a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f257 : InstrSpec 0x1078d8 [0x44, 0x88, 0x6C, 0x28, 0x21] (StorePre 0x1078d8 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x21)) s (0x1078d8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078d8 5 13 (.sib 0 (some 5) 0 (.d8 0x21)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1078d8 5 13 (.sib 0 (some 5) 0 (.d8 0x21))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1078d8 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x21)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f258 : InstrSpec 0x1078dd [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x59] (LoadPre 0x1078dd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x59)) s (0x1078dd + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078dd 6 13 (.sib 4 none 0 (.d8 0x59)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1078dd 6 13 (.sib 4 none 0 (.d8 0x59))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1078dd 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x59)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f259 : InstrSpec 0x1078e3 [0x44, 0x88, 0x6C, 0x28, 0x22] (StorePre 0x1078e3 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x22)) s (0x1078e3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078e3 5 13 (.sib 0 (some 5) 0 (.d8 0x22)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1078e3 5 13 (.sib 0 (some 5) 0 (.d8 0x22))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1078e3 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x22)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 452) (RestInside.out (n := 452) f240 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 453) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 452), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107880) f240 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 454) (RestInside.exec (n := 454) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 452), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107885) f241 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 455) (RestInside.out (n := 455) f242 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 456) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 455), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10788b) f242 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 457) (RestInside.exec (n := 457) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 455), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107890) f243 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 458) (RestInside.out (n := 458) f244 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 459) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 458), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107896) f244 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 460) (RestInside.exec (n := 460) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 458), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10789b) f245 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 461) (RestInside.out (n := 461) f246 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 462) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 461), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078a1) f246 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 463) (RestInside.exec (n := 463) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 461), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078a6) f247 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 464) (RestInside.out (n := 464) f248 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 465) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 464), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078ac) f248 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 466) (RestInside.exec (n := 466) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 464), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078b1) f249 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 467) (RestInside.out (n := 467) f250 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 468) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 467), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078b7) f250 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 469) (RestInside.exec (n := 469) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 467), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078bc) f251 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 470) (RestInside.out (n := 470) f252 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 471) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 470), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078c2) f252 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 472) (RestInside.exec (n := 472) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 470), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078c7) f253 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 473) (RestInside.out (n := 473) f254 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 474) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 473), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078cd) f254 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 475) (RestInside.exec (n := 475) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 473), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078d2) f255 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 476) (RestInside.out (n := 476) f256 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 477) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 476), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078d8) f256 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 478) (RestInside.exec (n := 478) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 476), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078dd) f257 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 479) (RestInside.out (n := 479) f258 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 480) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 479), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078e3) f258 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 481) (RestInside.exec (n := 481) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 479), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078e8) f259 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107315_13 code

theorem rest_l107315_11 [Bindings] (code : CodeMap) :
    Rest (n := 422) code lifted (codeRange 0x107315 bytes_l107315) [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 419), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]
      93 0x107809 bytes_l107315_11 b_l107315_11 := by
  have f220 : InstrSpec 0x107809 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x78] (LoadPre 0x107809 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107809 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107809 6 13 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107809 6 13 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107809 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f221 : InstrSpec 0x10780f [0x44, 0x88, 0x6C, 0x28, 0x0F] (StorePre 0x10780f 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xf)) s (0x10780f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10780f 5 13 (.sib 0 (some 5) 0 (.d8 0xf)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x10780f 5 13 (.sib 0 (some 5) 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10780f 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f222 : InstrSpec 0x107814 [0x44, 0x0F, 0xB6, 0xAC, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x107814 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107814 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107814 9 13 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107814 9 13 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107814 0x44 (by decide) 5 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f223 : InstrSpec 0x10781d [0x44, 0x88, 0x6C, 0x28, 0x10] (StorePre 0x10781d 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x10)) s (0x10781d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10781d 5 13 (.sib 0 (some 5) 0 (.d8 0x10)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x10781d 5 13 (.sib 0 (some 5) 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10781d 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f224 : InstrSpec 0x107822 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6A] (LoadPre 0x107822 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6a)) s (0x107822 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107822 6 13 (.sib 4 none 0 (.d8 0x6a)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107822 6 13 (.sib 4 none 0 (.d8 0x6a))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107822 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x6a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f225 : InstrSpec 0x107828 [0x44, 0x88, 0x6C, 0x28, 0x11] (StorePre 0x107828 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x11)) s (0x107828 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107828 5 13 (.sib 0 (some 5) 0 (.d8 0x11)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107828 5 13 (.sib 0 (some 5) 0 (.d8 0x11))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107828 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f226 : InstrSpec 0x10782d [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x69] (LoadPre 0x10782d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x69)) s (0x10782d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10782d 6 13 (.sib 4 none 0 (.d8 0x69)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x10782d 6 13 (.sib 4 none 0 (.d8 0x69))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10782d 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x69)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f227 : InstrSpec 0x107833 [0x44, 0x88, 0x6C, 0x28, 0x12] (StorePre 0x107833 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x12)) s (0x107833 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107833 5 13 (.sib 0 (some 5) 0 (.d8 0x12)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107833 5 13 (.sib 0 (some 5) 0 (.d8 0x12))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107833 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f228 : InstrSpec 0x107838 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x68] (LoadPre 0x107838 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x107838 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107838 6 13 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107838 6 13 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107838 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f229 : InstrSpec 0x10783e [0x44, 0x88, 0x6C, 0x28, 0x13] (StorePre 0x10783e 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x13)) s (0x10783e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10783e 5 13 (.sib 0 (some 5) 0 (.d8 0x13)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x10783e 5 13 (.sib 0 (some 5) 0 (.d8 0x13))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10783e 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f230 : InstrSpec 0x107843 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x67] (LoadPre 0x107843 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x67)) s (0x107843 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107843 6 13 (.sib 4 none 0 (.d8 0x67)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107843 6 13 (.sib 4 none 0 (.d8 0x67))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107843 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x67)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f231 : InstrSpec 0x107849 [0x44, 0x88, 0x6C, 0x28, 0x14] (StorePre 0x107849 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x14)) s (0x107849 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107849 5 13 (.sib 0 (some 5) 0 (.d8 0x14)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107849 5 13 (.sib 0 (some 5) 0 (.d8 0x14))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107849 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f232 : InstrSpec 0x10784e [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x66] (LoadPre 0x10784e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x10784e + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10784e 6 13 (.sib 4 none 0 (.d8 0x66)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x10784e 6 13 (.sib 4 none 0 (.d8 0x66))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10784e 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x66)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f233 : InstrSpec 0x107854 [0x44, 0x88, 0x6C, 0x28, 0x15] (StorePre 0x107854 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x15)) s (0x107854 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107854 5 13 (.sib 0 (some 5) 0 (.d8 0x15)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107854 5 13 (.sib 0 (some 5) 0 (.d8 0x15))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107854 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f234 : InstrSpec 0x107859 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x65] (LoadPre 0x107859 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x65)) s (0x107859 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107859 6 13 (.sib 4 none 0 (.d8 0x65)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107859 6 13 (.sib 4 none 0 (.d8 0x65))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107859 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x65)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f235 : InstrSpec 0x10785f [0x44, 0x88, 0x6C, 0x28, 0x16] (StorePre 0x10785f 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x16)) s (0x10785f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10785f 5 13 (.sib 0 (some 5) 0 (.d8 0x16)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x10785f 5 13 (.sib 0 (some 5) 0 (.d8 0x16))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10785f 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f236 : InstrSpec 0x107864 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x64] (LoadPre 0x107864 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x107864 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107864 6 13 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107864 6 13 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107864 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f237 : InstrSpec 0x10786a [0x44, 0x88, 0x6C, 0x28, 0x17] (StorePre 0x10786a 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x17)) s (0x10786a + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10786a 5 13 (.sib 0 (some 5) 0 (.d8 0x17)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x10786a 5 13 (.sib 0 (some 5) 0 (.d8 0x17))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10786a 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x17)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f238 : InstrSpec 0x10786f [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x63] (LoadPre 0x10786f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x63)) s (0x10786f + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10786f 6 13 (.sib 4 none 0 (.d8 0x63)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x10786f 6 13 (.sib 4 none 0 (.d8 0x63))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10786f 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x63)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f239 : InstrSpec 0x107875 [0x44, 0x88, 0x6C, 0x28, 0x18] (StorePre 0x107875 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x18)) s (0x107875 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107875 5 13 (.sib 0 (some 5) 0 (.d8 0x18)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107875 5 13 (.sib 0 (some 5) 0 (.d8 0x18))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107875 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 422) (RestInside.out (n := 422) f220 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 423) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 422), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10780f) f220 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 424) (RestInside.exec (n := 424) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 422), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107814) f221 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 425) (RestInside.out (n := 425) f222 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 426) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 425), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10781d) f222 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 427) (RestInside.exec (n := 427) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 425), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107822) f223 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 428) (RestInside.out (n := 428) f224 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 429) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 428), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107828) f224 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 430) (RestInside.exec (n := 430) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 428), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10782d) f225 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 431) (RestInside.out (n := 431) f226 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 432) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 431), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107833) f226 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 433) (RestInside.exec (n := 433) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 431), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107838) f227 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 434) (RestInside.out (n := 434) f228 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 435) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 434), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10783e) f228 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 436) (RestInside.exec (n := 436) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 434), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107843) f229 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 437) (RestInside.out (n := 437) f230 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 438) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 437), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107849) f230 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 439) (RestInside.exec (n := 439) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 437), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10784e) f231 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 440) (RestInside.out (n := 440) f232 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 441) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 440), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107854) f232 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 442) (RestInside.exec (n := 442) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 440), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107859) f233 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 443) (RestInside.out (n := 443) f234 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 444) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 443), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10785f) f234 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 445) (RestInside.exec (n := 445) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 443), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107864) f235 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 446) (RestInside.out (n := 446) f236 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 447) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 446), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10786a) f236 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 448) (RestInside.exec (n := 448) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 446), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10786f) f237 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 449) (RestInside.out (n := 449) f238 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 450) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 449), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107875) f238 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 451) (RestInside.exec (n := 451) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 449), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10787a) f239 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107315_12 code

theorem rest_l107315_10 [Bindings] (code : CodeMap) :
    Rest (n := 392) code lifted (codeRange 0x107315 bytes_l107315) [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 389), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]
      113 0x107795 bytes_l107315_10 b_l107315_10 := by
  have f200 : InstrSpec 0x107795 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x72] (LoadPre 0x107795 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x107795 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107795 6 13 (.sib 4 none 0 (.d8 0x72)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107795 6 13 (.sib 4 none 0 (.d8 0x72))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107795 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x72)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f201 : InstrSpec 0x10779b [0x44, 0x88, 0x6C, 0x28, 0x05] (StorePre 0x10779b 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x5)) s (0x10779b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10779b 5 13 (.sib 0 (some 5) 0 (.d8 0x5)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x10779b 5 13 (.sib 0 (some 5) 0 (.d8 0x5))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10779b 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f202 : InstrSpec 0x1077a0 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x71] (LoadPre 0x1077a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x71)) s (0x1077a0 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1077a0 6 13 (.sib 4 none 0 (.d8 0x71)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1077a0 6 13 (.sib 4 none 0 (.d8 0x71))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1077a0 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x71)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f203 : InstrSpec 0x1077a6 [0x44, 0x88, 0x6C, 0x28, 0x06] (StorePre 0x1077a6 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x6)) s (0x1077a6 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1077a6 5 13 (.sib 0 (some 5) 0 (.d8 0x6)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1077a6 5 13 (.sib 0 (some 5) 0 (.d8 0x6))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1077a6 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f204 : InstrSpec 0x1077ab [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x70] (LoadPre 0x1077ab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1077ab + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1077ab 6 13 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1077ab 6 13 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1077ab 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f205 : InstrSpec 0x1077b1 [0x44, 0x88, 0x6C, 0x28, 0x07] (StorePre 0x1077b1 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x7)) s (0x1077b1 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1077b1 5 13 (.sib 0 (some 5) 0 (.d8 0x7)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1077b1 5 13 (.sib 0 (some 5) 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1077b1 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f206 : InstrSpec 0x1077b6 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6F] (LoadPre 0x1077b6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6f)) s (0x1077b6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1077b6 6 13 (.sib 4 none 0 (.d8 0x6f)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1077b6 6 13 (.sib 4 none 0 (.d8 0x6f))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1077b6 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x6f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f207 : InstrSpec 0x1077bc [0x44, 0x88, 0x6C, 0x28, 0x08] (StorePre 0x1077bc 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x8)) s (0x1077bc + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1077bc 5 13 (.sib 0 (some 5) 0 (.d8 0x8)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1077bc 5 13 (.sib 0 (some 5) 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1077bc 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f208 : InstrSpec 0x1077c1 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6E] (LoadPre 0x1077c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6e)) s (0x1077c1 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1077c1 6 13 (.sib 4 none 0 (.d8 0x6e)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1077c1 6 13 (.sib 4 none 0 (.d8 0x6e))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1077c1 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x6e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f209 : InstrSpec 0x1077c7 [0x44, 0x88, 0x6C, 0x28, 0x09] (StorePre 0x1077c7 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x9)) s (0x1077c7 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1077c7 5 13 (.sib 0 (some 5) 0 (.d8 0x9)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1077c7 5 13 (.sib 0 (some 5) 0 (.d8 0x9))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1077c7 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f210 : InstrSpec 0x1077cc [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6D] (LoadPre 0x1077cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6d)) s (0x1077cc + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1077cc 6 13 (.sib 4 none 0 (.d8 0x6d)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1077cc 6 13 (.sib 4 none 0 (.d8 0x6d))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1077cc 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x6d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f211 : InstrSpec 0x1077d2 [0x44, 0x88, 0x6C, 0x28, 0x0A] (StorePre 0x1077d2 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xa)) s (0x1077d2 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1077d2 5 13 (.sib 0 (some 5) 0 (.d8 0xa)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1077d2 5 13 (.sib 0 (some 5) 0 (.d8 0xa))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1077d2 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f212 : InstrSpec 0x1077d7 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6C] (LoadPre 0x1077d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x1077d7 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1077d7 6 13 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1077d7 6 13 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1077d7 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f213 : InstrSpec 0x1077dd [0x44, 0x88, 0x6C, 0x28, 0x0B] (StorePre 0x1077dd 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xb)) s (0x1077dd + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1077dd 5 13 (.sib 0 (some 5) 0 (.d8 0xb)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1077dd 5 13 (.sib 0 (some 5) 0 (.d8 0xb))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1077dd 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f214 : InstrSpec 0x1077e2 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6B] (LoadPre 0x1077e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6b)) s (0x1077e2 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1077e2 6 13 (.sib 4 none 0 (.d8 0x6b)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1077e2 6 13 (.sib 4 none 0 (.d8 0x6b))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1077e2 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x6b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f215 : InstrSpec 0x1077e8 [0x44, 0x88, 0x6C, 0x28, 0x0C] (StorePre 0x1077e8 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xc)) s (0x1077e8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1077e8 5 13 (.sib 0 (some 5) 0 (.d8 0xc)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1077e8 5 13 (.sib 0 (some 5) 0 (.d8 0xc))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1077e8 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f216 : InstrSpec 0x1077ed [0x44, 0x0F, 0xB6, 0xAC, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x1077ed (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1077ed + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1077ed 9 13 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1077ed 9 13 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1077ed 0x44 (by decide) 5 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f217 : InstrSpec 0x1077f6 [0x44, 0x88, 0x6C, 0x28, 0x0D] (StorePre 0x1077f6 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xd)) s (0x1077f6 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1077f6 5 13 (.sib 0 (some 5) 0 (.d8 0xd)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x1077f6 5 13 (.sib 0 (some 5) 0 (.d8 0xd))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1077f6 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f218 : InstrSpec 0x1077fb [0x44, 0x0F, 0xB6, 0xAC, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x1077fb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1077fb + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1077fb 9 13 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1077fb 9 13 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1077fb 0x44 (by decide) 5 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f219 : InstrSpec 0x107804 [0x44, 0x88, 0x6C, 0x28, 0x0E] (StorePre 0x107804 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xe)) s (0x107804 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107804 5 13 (.sib 0 (some 5) 0 (.d8 0xe)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107804 5 13 (.sib 0 (some 5) 0 (.d8 0xe))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107804 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 392) (RestInside.out (n := 392) f200 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 393) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 392), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10779b) f200 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 394) (RestInside.exec (n := 394) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 392), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077a0) f201 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 395) (RestInside.out (n := 395) f202 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 396) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 395), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077a6) f202 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 397) (RestInside.exec (n := 397) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 395), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077ab) f203 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 398) (RestInside.out (n := 398) f204 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 399) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 398), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077b1) f204 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 400) (RestInside.exec (n := 400) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 398), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077b6) f205 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 401) (RestInside.out (n := 401) f206 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 402) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 401), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077bc) f206 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 403) (RestInside.exec (n := 403) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 401), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077c1) f207 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 404) (RestInside.out (n := 404) f208 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 405) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 404), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077c7) f208 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 406) (RestInside.exec (n := 406) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 404), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077cc) f209 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 407) (RestInside.out (n := 407) f210 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 408) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 407), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077d2) f210 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 409) (RestInside.exec (n := 409) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 407), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077d7) f211 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 410) (RestInside.out (n := 410) f212 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 411) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 410), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077dd) f212 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 412) (RestInside.exec (n := 412) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 410), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077e2) f213 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 413) (RestInside.out (n := 413) f214 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 414) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 413), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077e8) f214 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 415) (RestInside.exec (n := 415) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 413), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077ed) f215 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 416) (RestInside.out (n := 416) f216 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 417) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 416), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077f6) f216 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 418) (RestInside.exec (n := 418) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 416), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077fb) f217 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 419) (RestInside.out (n := 419) f218 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 420) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 419), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107804) f218 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 421) (RestInside.exec (n := 421) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 419), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107809) f219 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107315_11 code

theorem rest_l107315_9 [Bindings] (code : CodeMap) :
    Rest (n := 357) code lifted (codeRange 0x107315 bytes_l107315) [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 355), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]
      133 0x107720 bytes_l107315_9 b_l107315_9 := by
  have f180 : InstrSpec 0x107720 [0x44, 0x32, 0x44, 0x28, 0x3B] (LoadPre 0x107720 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3b)) s (0x107720 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x107720 5 8 (.sib 0 (some 5) 0 (.d8 0x3b)))
      [.gpr 8, .gpr 0, .gpr 5] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x107720 5 8 (.sib 0 (some 5) 0 (.d8 0x3b))).toInstrSpec (xor_r8_m8_rex_effect_step 0x107720 0x44 (by decide) 0 (.sib 0 (some 5) 0 (.d8 0x3b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f181 : InstrSpec 0x107725 [0x0F, 0xB6, 0xBC, 0x24, 0xD4, 0x00, 0x00, 0x00] (LoadPre 0x107725 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd4)) s (0x107725 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107725 8 7 (.sib 4 none 0 (.d32 0xd4)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x107725 8 7 (.sib 4 none 0 (.d32 0xd4))).toInstrSpec (movzx_r32_m8_effect_step 0x107725 7 (.sib 4 none 0 (.d32 0xd4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f182 : InstrSpec 0x10772d [0x40, 0x32, 0x7C, 0x28, 0x3C] (LoadPre 0x10772d (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3c)) s (0x10772d + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x10772d 5 7 (.sib 0 (some 5) 0 (.d8 0x3c)))
      [.gpr 7, .gpr 0, .gpr 5] [] [.reg 7, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10772d 5 7 (.sib 0 (some 5) 0 (.d8 0x3c))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10772d 0x40 (by decide) 7 (.sib 0 (some 5) 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f183 : InstrSpec 0x107732 [0x0F, 0xB6, 0xB4, 0x24, 0xD5, 0x00, 0x00, 0x00] (LoadPre 0x107732 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd5)) s (0x107732 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107732 8 6 (.sib 4 none 0 (.d32 0xd5)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x107732 8 6 (.sib 4 none 0 (.d32 0xd5))).toInstrSpec (movzx_r32_m8_effect_step 0x107732 6 (.sib 4 none 0 (.d32 0xd5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f184 : InstrSpec 0x10773a [0x40, 0x32, 0x74, 0x28, 0x3D] (LoadPre 0x10773a (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3d)) s (0x10773a + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x10773a 5 6 (.sib 0 (some 5) 0 (.d8 0x3d)))
      [.gpr 6, .gpr 0, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10773a 5 6 (.sib 0 (some 5) 0 (.d8 0x3d))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10773a 0x40 (by decide) 6 (.sib 0 (some 5) 0 (.d8 0x3d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f185 : InstrSpec 0x10773f [0x0F, 0xB6, 0x94, 0x24, 0xD6, 0x00, 0x00, 0x00] (LoadPre 0x10773f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd6)) s (0x10773f + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10773f 8 2 (.sib 4 none 0 (.d32 0xd6)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x10773f 8 2 (.sib 4 none 0 (.d32 0xd6))).toInstrSpec (movzx_r32_m8_effect_step 0x10773f 2 (.sib 4 none 0 (.d32 0xd6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f186 : InstrSpec 0x107747 [0x32, 0x54, 0x28, 0x3E] (LoadPre 0x107747 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3e)) s (0x107747 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x107747 4 2 (.sib 0 (some 5) 0 (.d8 0x3e)))
      [.gpr 2, .gpr 0, .gpr 5] [] [.reg 2, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x107747 4 2 (.sib 0 (some 5) 0 (.d8 0x3e))).toInstrSpec (xor_r8_m8_effect_step 0x107747 2 (by decide) (.sib 0 (some 5) 0 (.d8 0x3e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f187 : InstrSpec 0x10774b [0x0F, 0xB6, 0x8C, 0x24, 0xD7, 0x00, 0x00, 0x00] (LoadPre 0x10774b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd7)) s (0x10774b + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10774b 8 1 (.sib 4 none 0 (.d32 0xd7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10774b 8 1 (.sib 4 none 0 (.d32 0xd7))).toInstrSpec (movzx_r32_m8_effect_step 0x10774b 1 (.sib 4 none 0 (.d32 0xd7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f188 : InstrSpec 0x107753 [0x32, 0x4C, 0x28, 0x3F] (LoadPre 0x107753 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3f)) s (0x107753 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x107753 4 1 (.sib 0 (some 5) 0 (.d8 0x3f)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x107753 4 1 (.sib 0 (some 5) 0 (.d8 0x3f))).toInstrSpec (xor_r8_m8_effect_step 0x107753 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x3f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f189 : InstrSpec 0x107757 [0x48, 0x8B, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x107757 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x107757 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107757 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107757 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x107757 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f190 : InstrSpec 0x10775f [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x77] (LoadPre 0x10775f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x77)) s (0x10775f + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10775f 6 13 (.sib 4 none 0 (.d8 0x77)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x10775f 6 13 (.sib 4 none 0 (.d8 0x77))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10775f 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x77)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f191 : InstrSpec 0x107765 [0x44, 0x88, 0x2C, 0x28] (StorePre 0x107765 4 (fun s => AddrMode.addr (.sib 0 (some 5) 0 .none) s (0x107765 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107765 4 13 (.sib 0 (some 5) 0 .none))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107765 4 13 (.sib 0 (some 5) 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x107765 0x44 (by decide) 5 (.sib 0 (some 5) 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f192 : InstrSpec 0x107769 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x76] (LoadPre 0x107769 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x107769 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107769 6 13 (.sib 4 none 0 (.d8 0x76)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107769 6 13 (.sib 4 none 0 (.d8 0x76))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107769 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x76)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f193 : InstrSpec 0x10776f [0x44, 0x88, 0x6C, 0x28, 0x01] (StorePre 0x10776f 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1)) s (0x10776f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10776f 5 13 (.sib 0 (some 5) 0 (.d8 0x1)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x10776f 5 13 (.sib 0 (some 5) 0 (.d8 0x1))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10776f 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x1)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f194 : InstrSpec 0x107774 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x75] (LoadPre 0x107774 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x75)) s (0x107774 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107774 6 13 (.sib 4 none 0 (.d8 0x75)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107774 6 13 (.sib 4 none 0 (.d8 0x75))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107774 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x75)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f195 : InstrSpec 0x10777a [0x44, 0x88, 0x6C, 0x28, 0x02] (StorePre 0x10777a 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2)) s (0x10777a + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10777a 5 13 (.sib 0 (some 5) 0 (.d8 0x2)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x10777a 5 13 (.sib 0 (some 5) 0 (.d8 0x2))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10777a 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f196 : InstrSpec 0x10777f [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x74] (LoadPre 0x10777f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x10777f + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10777f 6 13 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x10777f 6 13 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10777f 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f197 : InstrSpec 0x107785 [0x44, 0x88, 0x6C, 0x28, 0x03] (StorePre 0x107785 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3)) s (0x107785 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107785 5 13 (.sib 0 (some 5) 0 (.d8 0x3)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107785 5 13 (.sib 0 (some 5) 0 (.d8 0x3))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107785 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f198 : InstrSpec 0x10778a [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x73] (LoadPre 0x10778a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x73)) s (0x10778a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10778a 6 13 (.sib 4 none 0 (.d8 0x73)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x10778a 6 13 (.sib 4 none 0 (.d8 0x73))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10778a 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x73)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f199 : InstrSpec 0x107790 [0x44, 0x88, 0x6C, 0x28, 0x04] (StorePre 0x107790 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x4)) s (0x107790 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107790 5 13 (.sib 0 (some 5) 0 (.d8 0x4)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x107790 5 13 (.sib 0 (some 5) 0 (.d8 0x4))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107790 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 357) (RestInside.out (n := 357) f180 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 358) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107725) f180 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 359) (RestInside.out (n := 359) f181 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 360) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 359), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10772d) f181 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 361) (RestInside.out (n := 361) f182 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 362) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107732) f182 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 363) (RestInside.out (n := 363) f183 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 364) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 363), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10773a) f183 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 365) (RestInside.out (n := 365) f184 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 366) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10773f) f184 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 367) (RestInside.out (n := 367) f185 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 368) (ρ' := [(0, 91), (1, 324), (2, 367), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107747) f185 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 369) (RestInside.out (n := 369) f186 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 370) (ρ' := [(0, 91), (1, 324), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10774b) f186 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 371) (RestInside.out (n := 371) f187 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 372) (ρ' := [(0, 91), (1, 371), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107753) f187 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 373) (RestInside.out (n := 373) f188 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 374) (ρ' := [(0, 91), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107757) f188 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 375) (RestInside.out (n := 375) f189 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 376) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10775f) f189 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 377) (RestInside.out (n := 377) f190 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 378) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 377), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107765) f190 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 379) (RestInside.exec (n := 379) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 377), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107769) f191 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 380) (RestInside.out (n := 380) f192 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 381) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 380), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10776f) f192 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 382) (RestInside.exec (n := 382) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 380), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107774) f193 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 383) (RestInside.out (n := 383) f194 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 384) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 383), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10777a) f194 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 385) (RestInside.exec (n := 385) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 383), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10777f) f195 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 386) (RestInside.out (n := 386) f196 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 387) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 386), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107785) f196 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 388) (RestInside.exec (n := 388) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 386), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10778a) f197 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 389) (RestInside.out (n := 389) f198 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 390) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 389), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107790) f198 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 391) (RestInside.exec (n := 391) (ρ' := [(0, 375), (1, 373), (2, 369), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 353), (10, 349), (11, 345), (12, 329), (13, 389), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107795) f199 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107315_10 code

theorem rest_l107315_8 [Bindings] (code : CodeMap) :
    Rest (n := 319) code lifted (codeRange 0x107315 bytes_l107315) [(0, 91), (1, 317), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]
      153 0x10769f bytes_l107315_8 b_l107315_8 := by
  have f160 : InstrSpec 0x10769f [0x32, 0x4C, 0x28, 0x32] (LoadPre 0x10769f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x32)) s (0x10769f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10769f 4 1 (.sib 0 (some 5) 0 (.d8 0x32)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10769f 4 1 (.sib 0 (some 5) 0 (.d8 0x32))).toInstrSpec (xor_r8_m8_effect_step 0x10769f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x32)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f161 : InstrSpec 0x1076a3 [0x88, 0x4C, 0x24, 0x49] (StorePre 0x1076a3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x49)) s (0x1076a3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1076a3 4 1 (.sib 4 none 0 (.d8 0x49)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1076a3 4 1 (.sib 4 none 0 (.d8 0x49))).toInstrSpec (mov_m8_r8_effect_step 0x1076a3 1 (by decide) (.sib 4 none 0 (.d8 0x49)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f162 : InstrSpec 0x1076a7 [0x0F, 0xB6, 0x8C, 0x24, 0xCB, 0x00, 0x00, 0x00] (LoadPre 0x1076a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcb)) s (0x1076a7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1076a7 8 1 (.sib 4 none 0 (.d32 0xcb)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1076a7 8 1 (.sib 4 none 0 (.d32 0xcb))).toInstrSpec (movzx_r32_m8_effect_step 0x1076a7 1 (.sib 4 none 0 (.d32 0xcb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f163 : InstrSpec 0x1076af [0x32, 0x4C, 0x28, 0x33] (LoadPre 0x1076af (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x33)) s (0x1076af + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1076af 4 1 (.sib 0 (some 5) 0 (.d8 0x33)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1076af 4 1 (.sib 0 (some 5) 0 (.d8 0x33))).toInstrSpec (xor_r8_m8_effect_step 0x1076af 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x33)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f164 : InstrSpec 0x1076b3 [0x88, 0x4C, 0x24, 0x48] (StorePre 0x1076b3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1076b3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1076b3 4 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1076b3 4 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m8_r8_effect_step 0x1076b3 1 (by decide) (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f165 : InstrSpec 0x1076b7 [0x44, 0x0F, 0xB6, 0xA4, 0x24, 0xCC, 0x00, 0x00, 0x00] (LoadPre 0x1076b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc)) s (0x1076b7 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1076b7 9 12 (.sib 4 none 0 (.d32 0xcc)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x1076b7 9 12 (.sib 4 none 0 (.d32 0xcc))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1076b7 0x44 (by decide) 4 (.sib 4 none 0 (.d32 0xcc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f166 : InstrSpec 0x1076c0 [0x44, 0x32, 0x64, 0x28, 0x34] (LoadPre 0x1076c0 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x34)) s (0x1076c0 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1076c0 5 12 (.sib 0 (some 5) 0 (.d8 0x34)))
      [.gpr 12, .gpr 0, .gpr 5] [] [.reg 12, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1076c0 5 12 (.sib 0 (some 5) 0 (.d8 0x34))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1076c0 0x44 (by decide) 4 (.sib 0 (some 5) 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f167 : InstrSpec 0x1076c5 [0x44, 0x0F, 0xB6, 0xBC, 0x24, 0xCD, 0x00, 0x00, 0x00] (LoadPre 0x1076c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcd)) s (0x1076c5 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1076c5 9 15 (.sib 4 none 0 (.d32 0xcd)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x1076c5 9 15 (.sib 4 none 0 (.d32 0xcd))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1076c5 0x44 (by decide) 7 (.sib 4 none 0 (.d32 0xcd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f168 : InstrSpec 0x1076ce [0x44, 0x32, 0x7C, 0x28, 0x35] (LoadPre 0x1076ce (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x35)) s (0x1076ce + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1076ce 5 15 (.sib 0 (some 5) 0 (.d8 0x35)))
      [.gpr 15, .gpr 0, .gpr 5] [] [.reg 15, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1076ce 5 15 (.sib 0 (some 5) 0 (.d8 0x35))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1076ce 0x44 (by decide) 7 (.sib 0 (some 5) 0 (.d8 0x35)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f169 : InstrSpec 0x1076d3 [0x44, 0x0F, 0xB6, 0xB4, 0x24, 0xCE, 0x00, 0x00, 0x00] (LoadPre 0x1076d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xce)) s (0x1076d3 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1076d3 9 14 (.sib 4 none 0 (.d32 0xce)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x1076d3 9 14 (.sib 4 none 0 (.d32 0xce))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1076d3 0x44 (by decide) 6 (.sib 4 none 0 (.d32 0xce)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f170 : InstrSpec 0x1076dc [0x44, 0x32, 0x74, 0x28, 0x36] (LoadPre 0x1076dc (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x36)) s (0x1076dc + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1076dc 5 14 (.sib 0 (some 5) 0 (.d8 0x36)))
      [.gpr 14, .gpr 0, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1076dc 5 14 (.sib 0 (some 5) 0 (.d8 0x36))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1076dc 0x44 (by decide) 6 (.sib 0 (some 5) 0 (.d8 0x36)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f171 : InstrSpec 0x1076e1 [0x0F, 0xB6, 0x9C, 0x24, 0xCF, 0x00, 0x00, 0x00] (LoadPre 0x1076e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcf)) s (0x1076e1 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1076e1 8 3 (.sib 4 none 0 (.d32 0xcf)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x1076e1 8 3 (.sib 4 none 0 (.d32 0xcf))).toInstrSpec (movzx_r32_m8_effect_step 0x1076e1 3 (.sib 4 none 0 (.d32 0xcf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f172 : InstrSpec 0x1076e9 [0x32, 0x5C, 0x28, 0x37] (LoadPre 0x1076e9 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x37)) s (0x1076e9 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1076e9 4 3 (.sib 0 (some 5) 0 (.d8 0x37)))
      [.gpr 3, .gpr 0, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1076e9 4 3 (.sib 0 (some 5) 0 (.d8 0x37))).toInstrSpec (xor_r8_m8_effect_step 0x1076e9 3 (by decide) (.sib 0 (some 5) 0 (.d8 0x37)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f173 : InstrSpec 0x1076ed [0x44, 0x0F, 0xB6, 0x9C, 0x24, 0xD0, 0x00, 0x00, 0x00] (LoadPre 0x1076ed (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1076ed + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1076ed 9 11 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x1076ed 9 11 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1076ed 0x44 (by decide) 3 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f174 : InstrSpec 0x1076f6 [0x44, 0x32, 0x5C, 0x28, 0x38] (LoadPre 0x1076f6 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x38)) s (0x1076f6 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1076f6 5 11 (.sib 0 (some 5) 0 (.d8 0x38)))
      [.gpr 11, .gpr 0, .gpr 5] [] [.reg 11, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1076f6 5 11 (.sib 0 (some 5) 0 (.d8 0x38))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1076f6 0x44 (by decide) 3 (.sib 0 (some 5) 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f175 : InstrSpec 0x1076fb [0x44, 0x0F, 0xB6, 0x94, 0x24, 0xD1, 0x00, 0x00, 0x00] (LoadPre 0x1076fb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd1)) s (0x1076fb + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1076fb 9 10 (.sib 4 none 0 (.d32 0xd1)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x1076fb 9 10 (.sib 4 none 0 (.d32 0xd1))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1076fb 0x44 (by decide) 2 (.sib 4 none 0 (.d32 0xd1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f176 : InstrSpec 0x107704 [0x44, 0x32, 0x54, 0x28, 0x39] (LoadPre 0x107704 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x39)) s (0x107704 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x107704 5 10 (.sib 0 (some 5) 0 (.d8 0x39)))
      [.gpr 10, .gpr 0, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x107704 5 10 (.sib 0 (some 5) 0 (.d8 0x39))).toInstrSpec (xor_r8_m8_rex_effect_step 0x107704 0x44 (by decide) 2 (.sib 0 (some 5) 0 (.d8 0x39)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f177 : InstrSpec 0x107709 [0x44, 0x0F, 0xB6, 0x8C, 0x24, 0xD2, 0x00, 0x00, 0x00] (LoadPre 0x107709 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd2)) s (0x107709 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107709 9 9 (.sib 4 none 0 (.d32 0xd2)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x107709 9 9 (.sib 4 none 0 (.d32 0xd2))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107709 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0xd2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f178 : InstrSpec 0x107712 [0x44, 0x32, 0x4C, 0x28, 0x3A] (LoadPre 0x107712 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3a)) s (0x107712 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x107712 5 9 (.sib 0 (some 5) 0 (.d8 0x3a)))
      [.gpr 9, .gpr 0, .gpr 5] [] [.reg 9, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x107712 5 9 (.sib 0 (some 5) 0 (.d8 0x3a))).toInstrSpec (xor_r8_m8_rex_effect_step 0x107712 0x44 (by decide) 1 (.sib 0 (some 5) 0 (.d8 0x3a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f179 : InstrSpec 0x107717 [0x44, 0x0F, 0xB6, 0x84, 0x24, 0xD3, 0x00, 0x00, 0x00] (LoadPre 0x107717 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd3)) s (0x107717 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107717 9 8 (.sib 4 none 0 (.d32 0xd3)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x107717 9 8 (.sib 4 none 0 (.d32 0xd3))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107717 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0xd3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 319) (RestInside.out (n := 319) f160 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 320) (ρ' := [(0, 91), (1, 319), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076a3) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 321) (RestInside.exec (n := 321) (ρ' := [(0, 91), (1, 319), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076a7) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 322) (RestInside.out (n := 322) f162 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 323) (ρ' := [(0, 91), (1, 322), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076af) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 324) (RestInside.out (n := 324) f163 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 325) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076b3) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 326) (RestInside.exec (n := 326) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076b7) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 327) (RestInside.out (n := 327) f165 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 328) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 327), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076c0) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 329) (RestInside.out (n := 329) f166 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 330) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 329), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076c5) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 331) (RestInside.out (n := 331) f167 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 332) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 329), (13, 129), (14, 120), (15, 331), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076ce) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 333) (RestInside.out (n := 333) f168 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 334) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 329), (13, 129), (14, 120), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076d3) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 335) (RestInside.out (n := 335) f169 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 336) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 329), (13, 129), (14, 335), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076dc) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 337) (RestInside.out (n := 337) f170 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 338) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076e1) f170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 339) (RestInside.out (n := 339) f171 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 340) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 339), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076e9) f171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 341) (RestInside.out (n := 341) f172 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 342) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076ed) f172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 343) (RestInside.out (n := 343) f173 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 344) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 343), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076f6) f173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 345) (RestInside.out (n := 345) f174 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 346) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076fb) f174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 347) (RestInside.out (n := 347) f175 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 348) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 347), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107704) f175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 349) (RestInside.out (n := 349) f176 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 350) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107709) f176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 351) (RestInside.out (n := 351) f177 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 352) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 351), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107712) f177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 353) (RestInside.out (n := 353) f178 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 354) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107717) f178 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 355) (RestInside.out (n := 355) f179 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 356) (ρ' := [(0, 91), (1, 324), (2, 96), (3, 341), (4, 4), (5, 5), (6, 99), (7, 102), (8, 355), (9, 353), (10, 349), (11, 345), (12, 329), (13, 129), (14, 337), (15, 333), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107720) f179 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107315_9 code

theorem rest_l107315_7 [Bindings] (code : CodeMap) :
    Rest (n := 286) code lifted (codeRange 0x107315 bytes_l107315) [(0, 91), (1, 284), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]
      173 0x107633 bytes_l107315_7 b_l107315_7 := by
  have f140 : InstrSpec 0x107633 [0x88, 0x4C, 0x24, 0x50] (StorePre 0x107633 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x107633 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107633 4 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107633 4 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m8_r8_effect_step 0x107633 1 (by decide) (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f141 : InstrSpec 0x107637 [0x0F, 0xB6, 0x8C, 0x24, 0xC4, 0x00, 0x00, 0x00] (LoadPre 0x107637 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc4)) s (0x107637 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107637 8 1 (.sib 4 none 0 (.d32 0xc4)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107637 8 1 (.sib 4 none 0 (.d32 0xc4))).toInstrSpec (movzx_r32_m8_effect_step 0x107637 1 (.sib 4 none 0 (.d32 0xc4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f142 : InstrSpec 0x10763f [0x32, 0x4C, 0x28, 0x2C] (LoadPre 0x10763f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2c)) s (0x10763f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10763f 4 1 (.sib 0 (some 5) 0 (.d8 0x2c)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10763f 4 1 (.sib 0 (some 5) 0 (.d8 0x2c))).toInstrSpec (xor_r8_m8_effect_step 0x10763f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f143 : InstrSpec 0x107643 [0x88, 0x4C, 0x24, 0x4F] (StorePre 0x107643 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x107643 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107643 4 1 (.sib 4 none 0 (.d8 0x4f)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107643 4 1 (.sib 4 none 0 (.d8 0x4f))).toInstrSpec (mov_m8_r8_effect_step 0x107643 1 (by decide) (.sib 4 none 0 (.d8 0x4f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f144 : InstrSpec 0x107647 [0x0F, 0xB6, 0x8C, 0x24, 0xC5, 0x00, 0x00, 0x00] (LoadPre 0x107647 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc5)) s (0x107647 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107647 8 1 (.sib 4 none 0 (.d32 0xc5)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107647 8 1 (.sib 4 none 0 (.d32 0xc5))).toInstrSpec (movzx_r32_m8_effect_step 0x107647 1 (.sib 4 none 0 (.d32 0xc5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f145 : InstrSpec 0x10764f [0x32, 0x4C, 0x28, 0x2D] (LoadPre 0x10764f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2d)) s (0x10764f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10764f 4 1 (.sib 0 (some 5) 0 (.d8 0x2d)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10764f 4 1 (.sib 0 (some 5) 0 (.d8 0x2d))).toInstrSpec (xor_r8_m8_effect_step 0x10764f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f146 : InstrSpec 0x107653 [0x88, 0x4C, 0x24, 0x4E] (StorePre 0x107653 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4e)) s (0x107653 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107653 4 1 (.sib 4 none 0 (.d8 0x4e)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107653 4 1 (.sib 4 none 0 (.d8 0x4e))).toInstrSpec (mov_m8_r8_effect_step 0x107653 1 (by decide) (.sib 4 none 0 (.d8 0x4e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f147 : InstrSpec 0x107657 [0x0F, 0xB6, 0x8C, 0x24, 0xC6, 0x00, 0x00, 0x00] (LoadPre 0x107657 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc6)) s (0x107657 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107657 8 1 (.sib 4 none 0 (.d32 0xc6)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107657 8 1 (.sib 4 none 0 (.d32 0xc6))).toInstrSpec (movzx_r32_m8_effect_step 0x107657 1 (.sib 4 none 0 (.d32 0xc6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f148 : InstrSpec 0x10765f [0x32, 0x4C, 0x28, 0x2E] (LoadPre 0x10765f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2e)) s (0x10765f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10765f 4 1 (.sib 0 (some 5) 0 (.d8 0x2e)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10765f 4 1 (.sib 0 (some 5) 0 (.d8 0x2e))).toInstrSpec (xor_r8_m8_effect_step 0x10765f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x2e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f149 : InstrSpec 0x107663 [0x88, 0x4C, 0x24, 0x4D] (StorePre 0x107663 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x107663 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107663 4 1 (.sib 4 none 0 (.d8 0x4d)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107663 4 1 (.sib 4 none 0 (.d8 0x4d))).toInstrSpec (mov_m8_r8_effect_step 0x107663 1 (by decide) (.sib 4 none 0 (.d8 0x4d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f150 : InstrSpec 0x107667 [0x0F, 0xB6, 0x8C, 0x24, 0xC7, 0x00, 0x00, 0x00] (LoadPre 0x107667 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc7)) s (0x107667 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107667 8 1 (.sib 4 none 0 (.d32 0xc7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107667 8 1 (.sib 4 none 0 (.d32 0xc7))).toInstrSpec (movzx_r32_m8_effect_step 0x107667 1 (.sib 4 none 0 (.d32 0xc7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f151 : InstrSpec 0x10766f [0x32, 0x4C, 0x28, 0x2F] (LoadPre 0x10766f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2f)) s (0x10766f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10766f 4 1 (.sib 0 (some 5) 0 (.d8 0x2f)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10766f 4 1 (.sib 0 (some 5) 0 (.d8 0x2f))).toInstrSpec (xor_r8_m8_effect_step 0x10766f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x2f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f152 : InstrSpec 0x107673 [0x88, 0x4C, 0x24, 0x4C] (StorePre 0x107673 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x107673 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107673 4 1 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107673 4 1 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_m8_r8_effect_step 0x107673 1 (by decide) (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f153 : InstrSpec 0x107677 [0x0F, 0xB6, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x107677 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x107677 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107677 8 1 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107677 8 1 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (movzx_r32_m8_effect_step 0x107677 1 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f154 : InstrSpec 0x10767f [0x32, 0x4C, 0x28, 0x30] (LoadPre 0x10767f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x30)) s (0x10767f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10767f 4 1 (.sib 0 (some 5) 0 (.d8 0x30)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10767f 4 1 (.sib 0 (some 5) 0 (.d8 0x30))).toInstrSpec (xor_r8_m8_effect_step 0x10767f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f155 : InstrSpec 0x107683 [0x88, 0x4C, 0x24, 0x4B] (StorePre 0x107683 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x107683 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107683 4 1 (.sib 4 none 0 (.d8 0x4b)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107683 4 1 (.sib 4 none 0 (.d8 0x4b))).toInstrSpec (mov_m8_r8_effect_step 0x107683 1 (by decide) (.sib 4 none 0 (.d8 0x4b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f156 : InstrSpec 0x107687 [0x0F, 0xB6, 0x8C, 0x24, 0xC9, 0x00, 0x00, 0x00] (LoadPre 0x107687 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc9)) s (0x107687 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107687 8 1 (.sib 4 none 0 (.d32 0xc9)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107687 8 1 (.sib 4 none 0 (.d32 0xc9))).toInstrSpec (movzx_r32_m8_effect_step 0x107687 1 (.sib 4 none 0 (.d32 0xc9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f157 : InstrSpec 0x10768f [0x32, 0x4C, 0x28, 0x31] (LoadPre 0x10768f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x31)) s (0x10768f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10768f 4 1 (.sib 0 (some 5) 0 (.d8 0x31)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10768f 4 1 (.sib 0 (some 5) 0 (.d8 0x31))).toInstrSpec (xor_r8_m8_effect_step 0x10768f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x31)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f158 : InstrSpec 0x107693 [0x88, 0x4C, 0x24, 0x4A] (StorePre 0x107693 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x107693 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107693 4 1 (.sib 4 none 0 (.d8 0x4a)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107693 4 1 (.sib 4 none 0 (.d8 0x4a))).toInstrSpec (mov_m8_r8_effect_step 0x107693 1 (by decide) (.sib 4 none 0 (.d8 0x4a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f159 : InstrSpec 0x107697 [0x0F, 0xB6, 0x8C, 0x24, 0xCA, 0x00, 0x00, 0x00] (LoadPre 0x107697 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xca)) s (0x107697 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107697 8 1 (.sib 4 none 0 (.d32 0xca)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107697 8 1 (.sib 4 none 0 (.d32 0xca))).toInstrSpec (movzx_r32_m8_effect_step 0x107697 1 (.sib 4 none 0 (.d32 0xca)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 286) (RestInside.exec (n := 286) (ρ' := [(0, 91), (1, 284), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107637) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 287) (RestInside.out (n := 287) f141 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 288) (ρ' := [(0, 91), (1, 287), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10763f) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 289) (RestInside.out (n := 289) f142 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 290) (ρ' := [(0, 91), (1, 289), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107643) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 291) (RestInside.exec (n := 291) (ρ' := [(0, 91), (1, 289), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107647) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 292) (RestInside.out (n := 292) f144 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 293) (ρ' := [(0, 91), (1, 292), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10764f) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 294) (RestInside.out (n := 294) f145 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 295) (ρ' := [(0, 91), (1, 294), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107653) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 296) (RestInside.exec (n := 296) (ρ' := [(0, 91), (1, 294), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107657) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 297) (RestInside.out (n := 297) f147 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 298) (ρ' := [(0, 91), (1, 297), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10765f) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 299) (RestInside.out (n := 299) f148 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 300) (ρ' := [(0, 91), (1, 299), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107663) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 301) (RestInside.exec (n := 301) (ρ' := [(0, 91), (1, 299), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107667) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f150 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 303) (ρ' := [(0, 91), (1, 302), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10766f) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f151 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 305) (ρ' := [(0, 91), (1, 304), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107673) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 306) (RestInside.exec (n := 306) (ρ' := [(0, 91), (1, 304), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107677) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 307) (RestInside.out (n := 307) f153 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 308) (ρ' := [(0, 91), (1, 307), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10767f) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 309) (RestInside.out (n := 309) f154 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 310) (ρ' := [(0, 91), (1, 309), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107683) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 311) (RestInside.exec (n := 311) (ρ' := [(0, 91), (1, 309), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107687) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 312) (RestInside.out (n := 312) f156 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 313) (ρ' := [(0, 91), (1, 312), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10768f) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 314) (RestInside.out (n := 314) f157 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 315) (ρ' := [(0, 91), (1, 314), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107693) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 316) (RestInside.exec (n := 316) (ρ' := [(0, 91), (1, 314), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107697) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 317) (RestInside.out (n := 317) f159 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 318) (ρ' := [(0, 91), (1, 317), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10769f) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107315_8 code

theorem rest_l107315_6 [Bindings] (code : CodeMap) :
    Rest (n := 252) code lifted (codeRange 0x107315 bytes_l107315) [(0, 91), (1, 249), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]
      193 0x1075c7 bytes_l107315_6 b_l107315_6 := by
  have f120 : InstrSpec 0x1075c7 [0x0F, 0xB6, 0x8C, 0x24, 0xBD, 0x00, 0x00, 0x00] (LoadPre 0x1075c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbd)) s (0x1075c7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075c7 8 1 (.sib 4 none 0 (.d32 0xbd)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1075c7 8 1 (.sib 4 none 0 (.d32 0xbd))).toInstrSpec (movzx_r32_m8_effect_step 0x1075c7 1 (.sib 4 none 0 (.d32 0xbd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f121 : InstrSpec 0x1075cf [0x32, 0x4C, 0x28, 0x25] (LoadPre 0x1075cf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x25)) s (0x1075cf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1075cf 4 1 (.sib 0 (some 5) 0 (.d8 0x25)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1075cf 4 1 (.sib 0 (some 5) 0 (.d8 0x25))).toInstrSpec (xor_r8_m8_effect_step 0x1075cf 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f122 : InstrSpec 0x1075d3 [0x88, 0x4C, 0x24, 0x56] (StorePre 0x1075d3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x56)) s (0x1075d3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075d3 4 1 (.sib 4 none 0 (.d8 0x56)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1075d3 4 1 (.sib 4 none 0 (.d8 0x56))).toInstrSpec (mov_m8_r8_effect_step 0x1075d3 1 (by decide) (.sib 4 none 0 (.d8 0x56)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f123 : InstrSpec 0x1075d7 [0x0F, 0xB6, 0x8C, 0x24, 0xBE, 0x00, 0x00, 0x00] (LoadPre 0x1075d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbe)) s (0x1075d7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075d7 8 1 (.sib 4 none 0 (.d32 0xbe)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1075d7 8 1 (.sib 4 none 0 (.d32 0xbe))).toInstrSpec (movzx_r32_m8_effect_step 0x1075d7 1 (.sib 4 none 0 (.d32 0xbe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f124 : InstrSpec 0x1075df [0x32, 0x4C, 0x28, 0x26] (LoadPre 0x1075df (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x26)) s (0x1075df + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1075df 4 1 (.sib 0 (some 5) 0 (.d8 0x26)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1075df 4 1 (.sib 0 (some 5) 0 (.d8 0x26))).toInstrSpec (xor_r8_m8_effect_step 0x1075df 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x26)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f125 : InstrSpec 0x1075e3 [0x88, 0x4C, 0x24, 0x55] (StorePre 0x1075e3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x55)) s (0x1075e3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075e3 4 1 (.sib 4 none 0 (.d8 0x55)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1075e3 4 1 (.sib 4 none 0 (.d8 0x55))).toInstrSpec (mov_m8_r8_effect_step 0x1075e3 1 (by decide) (.sib 4 none 0 (.d8 0x55)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f126 : InstrSpec 0x1075e7 [0x0F, 0xB6, 0x8C, 0x24, 0xBF, 0x00, 0x00, 0x00] (LoadPre 0x1075e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbf)) s (0x1075e7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075e7 8 1 (.sib 4 none 0 (.d32 0xbf)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1075e7 8 1 (.sib 4 none 0 (.d32 0xbf))).toInstrSpec (movzx_r32_m8_effect_step 0x1075e7 1 (.sib 4 none 0 (.d32 0xbf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f127 : InstrSpec 0x1075ef [0x32, 0x4C, 0x28, 0x27] (LoadPre 0x1075ef (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x27)) s (0x1075ef + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1075ef 4 1 (.sib 0 (some 5) 0 (.d8 0x27)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1075ef 4 1 (.sib 0 (some 5) 0 (.d8 0x27))).toInstrSpec (xor_r8_m8_effect_step 0x1075ef 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x27)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f128 : InstrSpec 0x1075f3 [0x88, 0x4C, 0x24, 0x54] (StorePre 0x1075f3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x1075f3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075f3 4 1 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1075f3 4 1 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_m8_r8_effect_step 0x1075f3 1 (by decide) (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f129 : InstrSpec 0x1075f7 [0x0F, 0xB6, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x1075f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1075f7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075f7 8 1 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1075f7 8 1 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (movzx_r32_m8_effect_step 0x1075f7 1 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f130 : InstrSpec 0x1075ff [0x32, 0x4C, 0x28, 0x28] (LoadPre 0x1075ff (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x28)) s (0x1075ff + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1075ff 4 1 (.sib 0 (some 5) 0 (.d8 0x28)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1075ff 4 1 (.sib 0 (some 5) 0 (.d8 0x28))).toInstrSpec (xor_r8_m8_effect_step 0x1075ff 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f131 : InstrSpec 0x107603 [0x88, 0x4C, 0x24, 0x53] (StorePre 0x107603 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x107603 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107603 4 1 (.sib 4 none 0 (.d8 0x53)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107603 4 1 (.sib 4 none 0 (.d8 0x53))).toInstrSpec (mov_m8_r8_effect_step 0x107603 1 (by decide) (.sib 4 none 0 (.d8 0x53)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f132 : InstrSpec 0x107607 [0x0F, 0xB6, 0x8C, 0x24, 0xC1, 0x00, 0x00, 0x00] (LoadPre 0x107607 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc1)) s (0x107607 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107607 8 1 (.sib 4 none 0 (.d32 0xc1)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107607 8 1 (.sib 4 none 0 (.d32 0xc1))).toInstrSpec (movzx_r32_m8_effect_step 0x107607 1 (.sib 4 none 0 (.d32 0xc1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f133 : InstrSpec 0x10760f [0x32, 0x4C, 0x28, 0x29] (LoadPre 0x10760f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x29)) s (0x10760f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10760f 4 1 (.sib 0 (some 5) 0 (.d8 0x29)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10760f 4 1 (.sib 0 (some 5) 0 (.d8 0x29))).toInstrSpec (xor_r8_m8_effect_step 0x10760f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x29)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f134 : InstrSpec 0x107613 [0x88, 0x4C, 0x24, 0x52] (StorePre 0x107613 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x52)) s (0x107613 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107613 4 1 (.sib 4 none 0 (.d8 0x52)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107613 4 1 (.sib 4 none 0 (.d8 0x52))).toInstrSpec (mov_m8_r8_effect_step 0x107613 1 (by decide) (.sib 4 none 0 (.d8 0x52)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f135 : InstrSpec 0x107617 [0x0F, 0xB6, 0x8C, 0x24, 0xC2, 0x00, 0x00, 0x00] (LoadPre 0x107617 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc2)) s (0x107617 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107617 8 1 (.sib 4 none 0 (.d32 0xc2)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107617 8 1 (.sib 4 none 0 (.d32 0xc2))).toInstrSpec (movzx_r32_m8_effect_step 0x107617 1 (.sib 4 none 0 (.d32 0xc2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f136 : InstrSpec 0x10761f [0x32, 0x4C, 0x28, 0x2A] (LoadPre 0x10761f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2a)) s (0x10761f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10761f 4 1 (.sib 0 (some 5) 0 (.d8 0x2a)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10761f 4 1 (.sib 0 (some 5) 0 (.d8 0x2a))).toInstrSpec (xor_r8_m8_effect_step 0x10761f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x2a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f137 : InstrSpec 0x107623 [0x88, 0x4C, 0x24, 0x51] (StorePre 0x107623 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x51)) s (0x107623 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107623 4 1 (.sib 4 none 0 (.d8 0x51)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107623 4 1 (.sib 4 none 0 (.d8 0x51))).toInstrSpec (mov_m8_r8_effect_step 0x107623 1 (by decide) (.sib 4 none 0 (.d8 0x51)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f138 : InstrSpec 0x107627 [0x0F, 0xB6, 0x8C, 0x24, 0xC3, 0x00, 0x00, 0x00] (LoadPre 0x107627 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc3)) s (0x107627 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107627 8 1 (.sib 4 none 0 (.d32 0xc3)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107627 8 1 (.sib 4 none 0 (.d32 0xc3))).toInstrSpec (movzx_r32_m8_effect_step 0x107627 1 (.sib 4 none 0 (.d32 0xc3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f139 : InstrSpec 0x10762f [0x32, 0x4C, 0x28, 0x2B] (LoadPre 0x10762f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2b)) s (0x10762f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10762f 4 1 (.sib 0 (some 5) 0 (.d8 0x2b)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10762f 4 1 (.sib 0 (some 5) 0 (.d8 0x2b))).toInstrSpec (xor_r8_m8_effect_step 0x10762f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x2b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 252) (RestInside.out (n := 252) f120 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 253) (ρ' := [(0, 91), (1, 252), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075cf) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 254) (RestInside.out (n := 254) f121 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 255) (ρ' := [(0, 91), (1, 254), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075d3) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 256) (RestInside.exec (n := 256) (ρ' := [(0, 91), (1, 254), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075d7) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 257) (RestInside.out (n := 257) f123 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 258) (ρ' := [(0, 91), (1, 257), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075df) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f124 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 260) (ρ' := [(0, 91), (1, 259), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075e3) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 261) (RestInside.exec (n := 261) (ρ' := [(0, 91), (1, 259), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075e7) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 262) (RestInside.out (n := 262) f126 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 263) (ρ' := [(0, 91), (1, 262), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075ef) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 264) (RestInside.out (n := 264) f127 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 265) (ρ' := [(0, 91), (1, 264), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075f3) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 266) (RestInside.exec (n := 266) (ρ' := [(0, 91), (1, 264), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075f7) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 267) (RestInside.out (n := 267) f129 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 268) (ρ' := [(0, 91), (1, 267), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075ff) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 269) (RestInside.out (n := 269) f130 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 270) (ρ' := [(0, 91), (1, 269), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107603) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 271) (RestInside.exec (n := 271) (ρ' := [(0, 91), (1, 269), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107607) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 272) (RestInside.out (n := 272) f132 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 273) (ρ' := [(0, 91), (1, 272), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10760f) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 274) (RestInside.out (n := 274) f133 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 275) (ρ' := [(0, 91), (1, 274), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107613) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 276) (RestInside.exec (n := 276) (ρ' := [(0, 91), (1, 274), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107617) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 277) (RestInside.out (n := 277) f135 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 278) (ρ' := [(0, 91), (1, 277), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10761f) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 279) (RestInside.out (n := 279) f136 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 280) (ρ' := [(0, 91), (1, 279), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107623) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 281) (RestInside.exec (n := 281) (ρ' := [(0, 91), (1, 279), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107627) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 282) (RestInside.out (n := 282) f138 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 283) (ρ' := [(0, 91), (1, 282), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10762f) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 284) (RestInside.out (n := 284) f139 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 285) (ρ' := [(0, 91), (1, 284), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107633) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107315_7 code

theorem rest_l107315_5 [Bindings] (code : CodeMap) :
    Rest (n := 219) code lifted (codeRange 0x107315 bytes_l107315) [(0, 91), (1, 217), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]
      213 0x10755f bytes_l107315_5 b_l107315_5 := by
  have f100 : InstrSpec 0x10755f [0x32, 0x4C, 0x28, 0x1E] (LoadPre 0x10755f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1e)) s (0x10755f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10755f 4 1 (.sib 0 (some 5) 0 (.d8 0x1e)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10755f 4 1 (.sib 0 (some 5) 0 (.d8 0x1e))).toInstrSpec (xor_r8_m8_effect_step 0x10755f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f101 : InstrSpec 0x107563 [0x88, 0x4C, 0x24, 0x5D] (StorePre 0x107563 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5d)) s (0x107563 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107563 4 1 (.sib 4 none 0 (.d8 0x5d)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107563 4 1 (.sib 4 none 0 (.d8 0x5d))).toInstrSpec (mov_m8_r8_effect_step 0x107563 1 (by decide) (.sib 4 none 0 (.d8 0x5d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f102 : InstrSpec 0x107567 [0x0F, 0xB6, 0x8C, 0x24, 0xB7, 0x00, 0x00, 0x00] (LoadPre 0x107567 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb7)) s (0x107567 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107567 8 1 (.sib 4 none 0 (.d32 0xb7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107567 8 1 (.sib 4 none 0 (.d32 0xb7))).toInstrSpec (movzx_r32_m8_effect_step 0x107567 1 (.sib 4 none 0 (.d32 0xb7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f103 : InstrSpec 0x10756f [0x32, 0x4C, 0x28, 0x1F] (LoadPre 0x10756f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1f)) s (0x10756f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10756f 4 1 (.sib 0 (some 5) 0 (.d8 0x1f)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10756f 4 1 (.sib 0 (some 5) 0 (.d8 0x1f))).toInstrSpec (xor_r8_m8_effect_step 0x10756f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f104 : InstrSpec 0x107573 [0x88, 0x4C, 0x24, 0x5C] (StorePre 0x107573 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x107573 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107573 4 1 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107573 4 1 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (mov_m8_r8_effect_step 0x107573 1 (by decide) (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f105 : InstrSpec 0x107577 [0x0F, 0xB6, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x107577 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x107577 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107577 8 1 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107577 8 1 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (movzx_r32_m8_effect_step 0x107577 1 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f106 : InstrSpec 0x10757f [0x32, 0x4C, 0x28, 0x20] (LoadPre 0x10757f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x20)) s (0x10757f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10757f 4 1 (.sib 0 (some 5) 0 (.d8 0x20)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10757f 4 1 (.sib 0 (some 5) 0 (.d8 0x20))).toInstrSpec (xor_r8_m8_effect_step 0x10757f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f107 : InstrSpec 0x107583 [0x88, 0x4C, 0x24, 0x5B] (StorePre 0x107583 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5b)) s (0x107583 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107583 4 1 (.sib 4 none 0 (.d8 0x5b)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107583 4 1 (.sib 4 none 0 (.d8 0x5b))).toInstrSpec (mov_m8_r8_effect_step 0x107583 1 (by decide) (.sib 4 none 0 (.d8 0x5b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f108 : InstrSpec 0x107587 [0x0F, 0xB6, 0x8C, 0x24, 0xB9, 0x00, 0x00, 0x00] (LoadPre 0x107587 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb9)) s (0x107587 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107587 8 1 (.sib 4 none 0 (.d32 0xb9)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107587 8 1 (.sib 4 none 0 (.d32 0xb9))).toInstrSpec (movzx_r32_m8_effect_step 0x107587 1 (.sib 4 none 0 (.d32 0xb9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f109 : InstrSpec 0x10758f [0x32, 0x4C, 0x28, 0x21] (LoadPre 0x10758f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x21)) s (0x10758f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10758f 4 1 (.sib 0 (some 5) 0 (.d8 0x21)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10758f 4 1 (.sib 0 (some 5) 0 (.d8 0x21))).toInstrSpec (xor_r8_m8_effect_step 0x10758f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x21)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f110 : InstrSpec 0x107593 [0x88, 0x4C, 0x24, 0x5A] (StorePre 0x107593 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5a)) s (0x107593 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107593 4 1 (.sib 4 none 0 (.d8 0x5a)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107593 4 1 (.sib 4 none 0 (.d8 0x5a))).toInstrSpec (mov_m8_r8_effect_step 0x107593 1 (by decide) (.sib 4 none 0 (.d8 0x5a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f111 : InstrSpec 0x107597 [0x0F, 0xB6, 0x8C, 0x24, 0xBA, 0x00, 0x00, 0x00] (LoadPre 0x107597 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xba)) s (0x107597 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107597 8 1 (.sib 4 none 0 (.d32 0xba)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107597 8 1 (.sib 4 none 0 (.d32 0xba))).toInstrSpec (movzx_r32_m8_effect_step 0x107597 1 (.sib 4 none 0 (.d32 0xba)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f112 : InstrSpec 0x10759f [0x32, 0x4C, 0x28, 0x22] (LoadPre 0x10759f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x22)) s (0x10759f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10759f 4 1 (.sib 0 (some 5) 0 (.d8 0x22)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10759f 4 1 (.sib 0 (some 5) 0 (.d8 0x22))).toInstrSpec (xor_r8_m8_effect_step 0x10759f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x22)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f113 : InstrSpec 0x1075a3 [0x88, 0x4C, 0x24, 0x59] (StorePre 0x1075a3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x59)) s (0x1075a3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075a3 4 1 (.sib 4 none 0 (.d8 0x59)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1075a3 4 1 (.sib 4 none 0 (.d8 0x59))).toInstrSpec (mov_m8_r8_effect_step 0x1075a3 1 (by decide) (.sib 4 none 0 (.d8 0x59)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f114 : InstrSpec 0x1075a7 [0x0F, 0xB6, 0x8C, 0x24, 0xBB, 0x00, 0x00, 0x00] (LoadPre 0x1075a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbb)) s (0x1075a7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075a7 8 1 (.sib 4 none 0 (.d32 0xbb)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1075a7 8 1 (.sib 4 none 0 (.d32 0xbb))).toInstrSpec (movzx_r32_m8_effect_step 0x1075a7 1 (.sib 4 none 0 (.d32 0xbb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f115 : InstrSpec 0x1075af [0x32, 0x4C, 0x28, 0x23] (LoadPre 0x1075af (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x23)) s (0x1075af + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1075af 4 1 (.sib 0 (some 5) 0 (.d8 0x23)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1075af 4 1 (.sib 0 (some 5) 0 (.d8 0x23))).toInstrSpec (xor_r8_m8_effect_step 0x1075af 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x23)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f116 : InstrSpec 0x1075b3 [0x88, 0x4C, 0x24, 0x58] (StorePre 0x1075b3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1075b3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075b3 4 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1075b3 4 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m8_r8_effect_step 0x1075b3 1 (by decide) (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f117 : InstrSpec 0x1075b7 [0x0F, 0xB6, 0x8C, 0x24, 0xBC, 0x00, 0x00, 0x00] (LoadPre 0x1075b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbc)) s (0x1075b7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075b7 8 1 (.sib 4 none 0 (.d32 0xbc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1075b7 8 1 (.sib 4 none 0 (.d32 0xbc))).toInstrSpec (movzx_r32_m8_effect_step 0x1075b7 1 (.sib 4 none 0 (.d32 0xbc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f118 : InstrSpec 0x1075bf [0x32, 0x4C, 0x28, 0x24] (LoadPre 0x1075bf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x24)) s (0x1075bf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1075bf 4 1 (.sib 0 (some 5) 0 (.d8 0x24)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1075bf 4 1 (.sib 0 (some 5) 0 (.d8 0x24))).toInstrSpec (xor_r8_m8_effect_step 0x1075bf 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f119 : InstrSpec 0x1075c3 [0x88, 0x4C, 0x24, 0x57] (StorePre 0x1075c3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x57)) s (0x1075c3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075c3 4 1 (.sib 4 none 0 (.d8 0x57)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1075c3 4 1 (.sib 4 none 0 (.d8 0x57))).toInstrSpec (mov_m8_r8_effect_step 0x1075c3 1 (by decide) (.sib 4 none 0 (.d8 0x57)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f100 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 91), (1, 219), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107563) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.exec (n := 221) (ρ' := [(0, 91), (1, 219), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107567) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 222) (RestInside.out (n := 222) f102 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 223) (ρ' := [(0, 91), (1, 222), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10756f) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 224) (RestInside.out (n := 224) f103 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 225) (ρ' := [(0, 91), (1, 224), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107573) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 226) (RestInside.exec (n := 226) (ρ' := [(0, 91), (1, 224), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107577) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f105 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 91), (1, 227), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10757f) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.out (n := 229) f106 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 230) (ρ' := [(0, 91), (1, 229), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107583) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.exec (n := 231) (ρ' := [(0, 91), (1, 229), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107587) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 232) (RestInside.out (n := 232) f108 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 233) (ρ' := [(0, 91), (1, 232), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10758f) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f109 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 91), (1, 234), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107593) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.exec (n := 236) (ρ' := [(0, 91), (1, 234), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107597) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 237) (RestInside.out (n := 237) f111 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 238) (ρ' := [(0, 91), (1, 237), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10759f) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 239) (RestInside.out (n := 239) f112 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 240) (ρ' := [(0, 91), (1, 239), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075a3) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 241) (RestInside.exec (n := 241) (ρ' := [(0, 91), (1, 239), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075a7) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 242) (RestInside.out (n := 242) f114 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 243) (ρ' := [(0, 91), (1, 242), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075af) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 244) (RestInside.out (n := 244) f115 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 245) (ρ' := [(0, 91), (1, 244), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075b3) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 246) (RestInside.exec (n := 246) (ρ' := [(0, 91), (1, 244), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075b7) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f117 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 248) (ρ' := [(0, 91), (1, 247), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075bf) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 249) (RestInside.out (n := 249) f118 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 250) (ρ' := [(0, 91), (1, 249), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075c3) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 251) (RestInside.exec (n := 251) (ρ' := [(0, 91), (1, 249), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075c7) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107315_6 code

theorem rest_l107315_4 [Bindings] (code : CodeMap) :
    Rest (n := 186) code lifted (codeRange 0x107315 bytes_l107315) [(0, 91), (1, 184), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]
      233 0x1074f3 bytes_l107315_4 b_l107315_4 := by
  have f80 : InstrSpec 0x1074f3 [0x88, 0x4C, 0x24, 0x64] (StorePre 0x1074f3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x1074f3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1074f3 4 1 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1074f3 4 1 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (mov_m8_r8_effect_step 0x1074f3 1 (by decide) (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f81 : InstrSpec 0x1074f7 [0x0F, 0xB6, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x1074f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1074f7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1074f7 8 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1074f7 8 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (movzx_r32_m8_effect_step 0x1074f7 1 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f82 : InstrSpec 0x1074ff [0x32, 0x4C, 0x28, 0x18] (LoadPre 0x1074ff (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x18)) s (0x1074ff + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1074ff 4 1 (.sib 0 (some 5) 0 (.d8 0x18)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1074ff 4 1 (.sib 0 (some 5) 0 (.d8 0x18))).toInstrSpec (xor_r8_m8_effect_step 0x1074ff 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f83 : InstrSpec 0x107503 [0x88, 0x4C, 0x24, 0x63] (StorePre 0x107503 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x63)) s (0x107503 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107503 4 1 (.sib 4 none 0 (.d8 0x63)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107503 4 1 (.sib 4 none 0 (.d8 0x63))).toInstrSpec (mov_m8_r8_effect_step 0x107503 1 (by decide) (.sib 4 none 0 (.d8 0x63)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f84 : InstrSpec 0x107507 [0x0F, 0xB6, 0x8C, 0x24, 0xB1, 0x00, 0x00, 0x00] (LoadPre 0x107507 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb1)) s (0x107507 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107507 8 1 (.sib 4 none 0 (.d32 0xb1)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107507 8 1 (.sib 4 none 0 (.d32 0xb1))).toInstrSpec (movzx_r32_m8_effect_step 0x107507 1 (.sib 4 none 0 (.d32 0xb1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f85 : InstrSpec 0x10750f [0x32, 0x4C, 0x28, 0x19] (LoadPre 0x10750f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x19)) s (0x10750f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10750f 4 1 (.sib 0 (some 5) 0 (.d8 0x19)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10750f 4 1 (.sib 0 (some 5) 0 (.d8 0x19))).toInstrSpec (xor_r8_m8_effect_step 0x10750f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f86 : InstrSpec 0x107513 [0x88, 0x4C, 0x24, 0x62] (StorePre 0x107513 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x107513 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107513 4 1 (.sib 4 none 0 (.d8 0x62)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107513 4 1 (.sib 4 none 0 (.d8 0x62))).toInstrSpec (mov_m8_r8_effect_step 0x107513 1 (by decide) (.sib 4 none 0 (.d8 0x62)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f87 : InstrSpec 0x107517 [0x0F, 0xB6, 0x8C, 0x24, 0xB2, 0x00, 0x00, 0x00] (LoadPre 0x107517 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb2)) s (0x107517 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107517 8 1 (.sib 4 none 0 (.d32 0xb2)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107517 8 1 (.sib 4 none 0 (.d32 0xb2))).toInstrSpec (movzx_r32_m8_effect_step 0x107517 1 (.sib 4 none 0 (.d32 0xb2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f88 : InstrSpec 0x10751f [0x32, 0x4C, 0x28, 0x1A] (LoadPre 0x10751f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1a)) s (0x10751f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10751f 4 1 (.sib 0 (some 5) 0 (.d8 0x1a)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10751f 4 1 (.sib 0 (some 5) 0 (.d8 0x1a))).toInstrSpec (xor_r8_m8_effect_step 0x10751f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f89 : InstrSpec 0x107523 [0x88, 0x4C, 0x24, 0x61] (StorePre 0x107523 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x61)) s (0x107523 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107523 4 1 (.sib 4 none 0 (.d8 0x61)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107523 4 1 (.sib 4 none 0 (.d8 0x61))).toInstrSpec (mov_m8_r8_effect_step 0x107523 1 (by decide) (.sib 4 none 0 (.d8 0x61)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f90 : InstrSpec 0x107527 [0x0F, 0xB6, 0x8C, 0x24, 0xB3, 0x00, 0x00, 0x00] (LoadPre 0x107527 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb3)) s (0x107527 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107527 8 1 (.sib 4 none 0 (.d32 0xb3)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107527 8 1 (.sib 4 none 0 (.d32 0xb3))).toInstrSpec (movzx_r32_m8_effect_step 0x107527 1 (.sib 4 none 0 (.d32 0xb3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f91 : InstrSpec 0x10752f [0x32, 0x4C, 0x28, 0x1B] (LoadPre 0x10752f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1b)) s (0x10752f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10752f 4 1 (.sib 0 (some 5) 0 (.d8 0x1b)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10752f 4 1 (.sib 0 (some 5) 0 (.d8 0x1b))).toInstrSpec (xor_r8_m8_effect_step 0x10752f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f92 : InstrSpec 0x107533 [0x88, 0x4C, 0x24, 0x60] (StorePre 0x107533 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x107533 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107533 4 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107533 4 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m8_r8_effect_step 0x107533 1 (by decide) (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f93 : InstrSpec 0x107537 [0x0F, 0xB6, 0x8C, 0x24, 0xB4, 0x00, 0x00, 0x00] (LoadPre 0x107537 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x107537 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107537 8 1 (.sib 4 none 0 (.d32 0xb4)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107537 8 1 (.sib 4 none 0 (.d32 0xb4))).toInstrSpec (movzx_r32_m8_effect_step 0x107537 1 (.sib 4 none 0 (.d32 0xb4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f94 : InstrSpec 0x10753f [0x32, 0x4C, 0x28, 0x1C] (LoadPre 0x10753f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1c)) s (0x10753f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10753f 4 1 (.sib 0 (some 5) 0 (.d8 0x1c)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10753f 4 1 (.sib 0 (some 5) 0 (.d8 0x1c))).toInstrSpec (xor_r8_m8_effect_step 0x10753f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f95 : InstrSpec 0x107543 [0x88, 0x4C, 0x24, 0x5F] (StorePre 0x107543 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5f)) s (0x107543 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107543 4 1 (.sib 4 none 0 (.d8 0x5f)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107543 4 1 (.sib 4 none 0 (.d8 0x5f))).toInstrSpec (mov_m8_r8_effect_step 0x107543 1 (by decide) (.sib 4 none 0 (.d8 0x5f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f96 : InstrSpec 0x107547 [0x0F, 0xB6, 0x8C, 0x24, 0xB5, 0x00, 0x00, 0x00] (LoadPre 0x107547 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb5)) s (0x107547 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107547 8 1 (.sib 4 none 0 (.d32 0xb5)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107547 8 1 (.sib 4 none 0 (.d32 0xb5))).toInstrSpec (movzx_r32_m8_effect_step 0x107547 1 (.sib 4 none 0 (.d32 0xb5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f97 : InstrSpec 0x10754f [0x32, 0x4C, 0x28, 0x1D] (LoadPre 0x10754f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1d)) s (0x10754f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10754f 4 1 (.sib 0 (some 5) 0 (.d8 0x1d)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10754f 4 1 (.sib 0 (some 5) 0 (.d8 0x1d))).toInstrSpec (xor_r8_m8_effect_step 0x10754f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f98 : InstrSpec 0x107553 [0x88, 0x4C, 0x24, 0x5E] (StorePre 0x107553 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x107553 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107553 4 1 (.sib 4 none 0 (.d8 0x5e)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107553 4 1 (.sib 4 none 0 (.d8 0x5e))).toInstrSpec (mov_m8_r8_effect_step 0x107553 1 (by decide) (.sib 4 none 0 (.d8 0x5e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f99 : InstrSpec 0x107557 [0x0F, 0xB6, 0x8C, 0x24, 0xB6, 0x00, 0x00, 0x00] (LoadPre 0x107557 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb6)) s (0x107557 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107557 8 1 (.sib 4 none 0 (.d32 0xb6)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107557 8 1 (.sib 4 none 0 (.d32 0xb6))).toInstrSpec (movzx_r32_m8_effect_step 0x107557 1 (.sib 4 none 0 (.d32 0xb6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 186) (RestInside.exec (n := 186) (ρ' := [(0, 91), (1, 184), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074f7) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f81 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 91), (1, 187), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074ff) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f82 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 91), (1, 189), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107503) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.exec (n := 191) (ρ' := [(0, 91), (1, 189), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107507) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 192) (RestInside.out (n := 192) f84 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 193) (ρ' := [(0, 91), (1, 192), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10750f) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 194) (RestInside.out (n := 194) f85 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 195) (ρ' := [(0, 91), (1, 194), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107513) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 196) (RestInside.exec (n := 196) (ρ' := [(0, 91), (1, 194), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107517) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f87 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 91), (1, 197), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10751f) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f88 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 91), (1, 199), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107523) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.exec (n := 201) (ρ' := [(0, 91), (1, 199), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107527) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f90 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 91), (1, 202), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10752f) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f91 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 91), (1, 204), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107533) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.exec (n := 206) (ρ' := [(0, 91), (1, 204), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107537) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 207) (RestInside.out (n := 207) f93 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 208) (ρ' := [(0, 91), (1, 207), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10753f) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 209) (RestInside.out (n := 209) f94 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 210) (ρ' := [(0, 91), (1, 209), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107543) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 211) (RestInside.exec (n := 211) (ρ' := [(0, 91), (1, 209), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107547) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f96 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 91), (1, 212), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10754f) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f97 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 91), (1, 214), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107553) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.exec (n := 216) (ρ' := [(0, 91), (1, 214), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107557) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 217) (RestInside.out (n := 217) f99 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 218) (ρ' := [(0, 91), (1, 217), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10755f) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107315_5 code

theorem rest_l107315_3 [Bindings] (code : CodeMap) :
    Rest (n := 152) code lifted (codeRange 0x107315 bytes_l107315) [(0, 91), (1, 149), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]
      253 0x107487 bytes_l107315_3 b_l107315_3 := by
  have f60 : InstrSpec 0x107487 [0x0F, 0xB6, 0x8C, 0x24, 0xA9, 0x00, 0x00, 0x00] (LoadPre 0x107487 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa9)) s (0x107487 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107487 8 1 (.sib 4 none 0 (.d32 0xa9)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107487 8 1 (.sib 4 none 0 (.d32 0xa9))).toInstrSpec (movzx_r32_m8_effect_step 0x107487 1 (.sib 4 none 0 (.d32 0xa9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f61 : InstrSpec 0x10748f [0x32, 0x4C, 0x28, 0x11] (LoadPre 0x10748f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x11)) s (0x10748f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10748f 4 1 (.sib 0 (some 5) 0 (.d8 0x11)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10748f 4 1 (.sib 0 (some 5) 0 (.d8 0x11))).toInstrSpec (xor_r8_m8_effect_step 0x10748f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f62 : InstrSpec 0x107493 [0x88, 0x4C, 0x24, 0x6A] (StorePre 0x107493 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6a)) s (0x107493 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107493 4 1 (.sib 4 none 0 (.d8 0x6a)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107493 4 1 (.sib 4 none 0 (.d8 0x6a))).toInstrSpec (mov_m8_r8_effect_step 0x107493 1 (by decide) (.sib 4 none 0 (.d8 0x6a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f63 : InstrSpec 0x107497 [0x0F, 0xB6, 0x8C, 0x24, 0xAA, 0x00, 0x00, 0x00] (LoadPre 0x107497 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaa)) s (0x107497 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107497 8 1 (.sib 4 none 0 (.d32 0xaa)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107497 8 1 (.sib 4 none 0 (.d32 0xaa))).toInstrSpec (movzx_r32_m8_effect_step 0x107497 1 (.sib 4 none 0 (.d32 0xaa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f64 : InstrSpec 0x10749f [0x32, 0x4C, 0x28, 0x12] (LoadPre 0x10749f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x12)) s (0x10749f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10749f 4 1 (.sib 0 (some 5) 0 (.d8 0x12)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10749f 4 1 (.sib 0 (some 5) 0 (.d8 0x12))).toInstrSpec (xor_r8_m8_effect_step 0x10749f 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f65 : InstrSpec 0x1074a3 [0x88, 0x4C, 0x24, 0x69] (StorePre 0x1074a3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x69)) s (0x1074a3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1074a3 4 1 (.sib 4 none 0 (.d8 0x69)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1074a3 4 1 (.sib 4 none 0 (.d8 0x69))).toInstrSpec (mov_m8_r8_effect_step 0x1074a3 1 (by decide) (.sib 4 none 0 (.d8 0x69)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f66 : InstrSpec 0x1074a7 [0x0F, 0xB6, 0x8C, 0x24, 0xAB, 0x00, 0x00, 0x00] (LoadPre 0x1074a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xab)) s (0x1074a7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1074a7 8 1 (.sib 4 none 0 (.d32 0xab)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1074a7 8 1 (.sib 4 none 0 (.d32 0xab))).toInstrSpec (movzx_r32_m8_effect_step 0x1074a7 1 (.sib 4 none 0 (.d32 0xab)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f67 : InstrSpec 0x1074af [0x32, 0x4C, 0x28, 0x13] (LoadPre 0x1074af (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x13)) s (0x1074af + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1074af 4 1 (.sib 0 (some 5) 0 (.d8 0x13)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1074af 4 1 (.sib 0 (some 5) 0 (.d8 0x13))).toInstrSpec (xor_r8_m8_effect_step 0x1074af 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f68 : InstrSpec 0x1074b3 [0x88, 0x4C, 0x24, 0x68] (StorePre 0x1074b3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1074b3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1074b3 4 1 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1074b3 4 1 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m8_r8_effect_step 0x1074b3 1 (by decide) (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f69 : InstrSpec 0x1074b7 [0x0F, 0xB6, 0x8C, 0x24, 0xAC, 0x00, 0x00, 0x00] (LoadPre 0x1074b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xac)) s (0x1074b7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1074b7 8 1 (.sib 4 none 0 (.d32 0xac)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1074b7 8 1 (.sib 4 none 0 (.d32 0xac))).toInstrSpec (movzx_r32_m8_effect_step 0x1074b7 1 (.sib 4 none 0 (.d32 0xac)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f70 : InstrSpec 0x1074bf [0x32, 0x4C, 0x28, 0x14] (LoadPre 0x1074bf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x14)) s (0x1074bf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1074bf 4 1 (.sib 0 (some 5) 0 (.d8 0x14)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1074bf 4 1 (.sib 0 (some 5) 0 (.d8 0x14))).toInstrSpec (xor_r8_m8_effect_step 0x1074bf 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f71 : InstrSpec 0x1074c3 [0x88, 0x4C, 0x24, 0x67] (StorePre 0x1074c3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x67)) s (0x1074c3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1074c3 4 1 (.sib 4 none 0 (.d8 0x67)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1074c3 4 1 (.sib 4 none 0 (.d8 0x67))).toInstrSpec (mov_m8_r8_effect_step 0x1074c3 1 (by decide) (.sib 4 none 0 (.d8 0x67)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f72 : InstrSpec 0x1074c7 [0x0F, 0xB6, 0x8C, 0x24, 0xAD, 0x00, 0x00, 0x00] (LoadPre 0x1074c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xad)) s (0x1074c7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1074c7 8 1 (.sib 4 none 0 (.d32 0xad)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1074c7 8 1 (.sib 4 none 0 (.d32 0xad))).toInstrSpec (movzx_r32_m8_effect_step 0x1074c7 1 (.sib 4 none 0 (.d32 0xad)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f73 : InstrSpec 0x1074cf [0x32, 0x4C, 0x28, 0x15] (LoadPre 0x1074cf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x15)) s (0x1074cf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1074cf 4 1 (.sib 0 (some 5) 0 (.d8 0x15)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1074cf 4 1 (.sib 0 (some 5) 0 (.d8 0x15))).toInstrSpec (xor_r8_m8_effect_step 0x1074cf 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f74 : InstrSpec 0x1074d3 [0x88, 0x4C, 0x24, 0x66] (StorePre 0x1074d3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x1074d3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1074d3 4 1 (.sib 4 none 0 (.d8 0x66)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1074d3 4 1 (.sib 4 none 0 (.d8 0x66))).toInstrSpec (mov_m8_r8_effect_step 0x1074d3 1 (by decide) (.sib 4 none 0 (.d8 0x66)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f75 : InstrSpec 0x1074d7 [0x0F, 0xB6, 0x8C, 0x24, 0xAE, 0x00, 0x00, 0x00] (LoadPre 0x1074d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xae)) s (0x1074d7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1074d7 8 1 (.sib 4 none 0 (.d32 0xae)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1074d7 8 1 (.sib 4 none 0 (.d32 0xae))).toInstrSpec (movzx_r32_m8_effect_step 0x1074d7 1 (.sib 4 none 0 (.d32 0xae)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f76 : InstrSpec 0x1074df [0x32, 0x4C, 0x28, 0x16] (LoadPre 0x1074df (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x16)) s (0x1074df + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1074df 4 1 (.sib 0 (some 5) 0 (.d8 0x16)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1074df 4 1 (.sib 0 (some 5) 0 (.d8 0x16))).toInstrSpec (xor_r8_m8_effect_step 0x1074df 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f77 : InstrSpec 0x1074e3 [0x88, 0x4C, 0x24, 0x65] (StorePre 0x1074e3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x65)) s (0x1074e3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1074e3 4 1 (.sib 4 none 0 (.d8 0x65)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1074e3 4 1 (.sib 4 none 0 (.d8 0x65))).toInstrSpec (mov_m8_r8_effect_step 0x1074e3 1 (by decide) (.sib 4 none 0 (.d8 0x65)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f78 : InstrSpec 0x1074e7 [0x0F, 0xB6, 0x8C, 0x24, 0xAF, 0x00, 0x00, 0x00] (LoadPre 0x1074e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaf)) s (0x1074e7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1074e7 8 1 (.sib 4 none 0 (.d32 0xaf)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1074e7 8 1 (.sib 4 none 0 (.d32 0xaf))).toInstrSpec (movzx_r32_m8_effect_step 0x1074e7 1 (.sib 4 none 0 (.d32 0xaf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f79 : InstrSpec 0x1074ef [0x32, 0x4C, 0x28, 0x17] (LoadPre 0x1074ef (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x17)) s (0x1074ef + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1074ef 4 1 (.sib 0 (some 5) 0 (.d8 0x17)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1074ef 4 1 (.sib 0 (some 5) 0 (.d8 0x17))).toInstrSpec (xor_r8_m8_effect_step 0x1074ef 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x17)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f60 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 91), (1, 152), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10748f) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f61 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 91), (1, 154), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107493) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.exec (n := 156) (ρ' := [(0, 91), (1, 154), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107497) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f63 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 91), (1, 157), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10749f) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f64 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 91), (1, 159), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074a3) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.exec (n := 161) (ρ' := [(0, 91), (1, 159), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074a7) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f66 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 91), (1, 162), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074af) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f67 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 91), (1, 164), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074b3) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.exec (n := 166) (ρ' := [(0, 91), (1, 164), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074b7) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f69 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 91), (1, 167), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074bf) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f70 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 91), (1, 169), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074c3) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.exec (n := 171) (ρ' := [(0, 91), (1, 169), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074c7) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f72 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 91), (1, 172), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074cf) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f73 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 91), (1, 174), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074d3) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.exec (n := 176) (ρ' := [(0, 91), (1, 174), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074d7) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f75 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 91), (1, 177), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074df) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f76 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 91), (1, 179), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074e3) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.exec (n := 181) (ρ' := [(0, 91), (1, 179), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074e7) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f78 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 91), (1, 182), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074ef) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f79 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(0, 91), (1, 184), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074f3) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107315_4 code

theorem rest_l107315_2 [Bindings] (code : CodeMap) :
    Rest (n := 120) code lifted (codeRange 0x107315 bytes_l107315) [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]
      273 0x107419 bytes_l107315_2 b_l107315_2 := by
  have f40 : InstrSpec 0x107419 [0x44, 0x32, 0x74, 0x28, 0x09] (LoadPre 0x107419 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x9)) s (0x107419 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x107419 5 14 (.sib 0 (some 5) 0 (.d8 0x9)))
      [.gpr 14, .gpr 0, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x107419 5 14 (.sib 0 (some 5) 0 (.d8 0x9))).toInstrSpec (xor_r8_m8_rex_effect_step 0x107419 0x44 (by decide) 6 (.sib 0 (some 5) 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x10741e [0x44, 0x88, 0x74, 0x24, 0x6E] (StorePre 0x10741e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6e)) s (0x10741e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10741e 5 14 (.sib 4 none 0 (.d8 0x6e)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10741e 5 14 (.sib 4 none 0 (.d8 0x6e))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10741e 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x6e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x107423 [0x44, 0x32, 0x7C, 0x28, 0x0A] (LoadPre 0x107423 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xa)) s (0x107423 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x107423 5 15 (.sib 0 (some 5) 0 (.d8 0xa)))
      [.gpr 15, .gpr 0, .gpr 5] [] [.reg 15, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x107423 5 15 (.sib 0 (some 5) 0 (.d8 0xa))).toInstrSpec (xor_r8_m8_rex_effect_step 0x107423 0x44 (by decide) 7 (.sib 0 (some 5) 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f43 : InstrSpec 0x107428 [0x44, 0x88, 0x7C, 0x24, 0x6D] (StorePre 0x107428 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6d)) s (0x107428 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107428 5 15 (.sib 4 none 0 (.d8 0x6d)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107428 5 15 (.sib 4 none 0 (.d8 0x6d))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107428 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x6d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f44 : InstrSpec 0x10742d [0x44, 0x32, 0x64, 0x28, 0x0B] (LoadPre 0x10742d (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xb)) s (0x10742d + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x10742d 5 12 (.sib 0 (some 5) 0 (.d8 0xb)))
      [.gpr 12, .gpr 0, .gpr 5] [] [.reg 12, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10742d 5 12 (.sib 0 (some 5) 0 (.d8 0xb))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10742d 0x44 (by decide) 4 (.sib 0 (some 5) 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f45 : InstrSpec 0x107432 [0x44, 0x88, 0x64, 0x24, 0x6C] (StorePre 0x107432 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x107432 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107432 5 12 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107432 5 12 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107432 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f46 : InstrSpec 0x107437 [0x44, 0x32, 0x6C, 0x28, 0x0C] (LoadPre 0x107437 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xc)) s (0x107437 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x107437 5 13 (.sib 0 (some 5) 0 (.d8 0xc)))
      [.gpr 13, .gpr 0, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x107437 5 13 (.sib 0 (some 5) 0 (.d8 0xc))).toInstrSpec (xor_r8_m8_rex_effect_step 0x107437 0x44 (by decide) 5 (.sib 0 (some 5) 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f47 : InstrSpec 0x10743c [0x44, 0x88, 0x6C, 0x24, 0x6B] (StorePre 0x10743c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6b)) s (0x10743c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10743c 5 13 (.sib 4 none 0 (.d8 0x6b)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10743c 5 13 (.sib 4 none 0 (.d8 0x6b))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10743c 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x6b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x107441 [0x0F, 0xB6, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x107441 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107441 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107441 8 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107441 8 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (movzx_r32_m8_effect_step 0x107441 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f49 : InstrSpec 0x107449 [0x32, 0x4C, 0x28, 0x0D] (LoadPre 0x107449 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xd)) s (0x107449 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x107449 4 1 (.sib 0 (some 5) 0 (.d8 0xd)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x107449 4 1 (.sib 0 (some 5) 0 (.d8 0xd))).toInstrSpec (xor_r8_m8_effect_step 0x107449 1 (by decide) (.sib 0 (some 5) 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f50 : InstrSpec 0x10744d [0x88, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x10744d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10744d + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10744d 7 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10744d 7 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m8_r8_effect_step 0x10744d 1 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f51 : InstrSpec 0x107454 [0x0F, 0xB6, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x107454 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x107454 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107454 8 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107454 8 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (movzx_r32_m8_effect_step 0x107454 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f52 : InstrSpec 0x10745c [0x32, 0x4C, 0x28, 0x0E] (LoadPre 0x10745c (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xe)) s (0x10745c + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10745c 4 1 (.sib 0 (some 5) 0 (.d8 0xe)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10745c 4 1 (.sib 0 (some 5) 0 (.d8 0xe))).toInstrSpec (xor_r8_m8_effect_step 0x10745c 1 (by decide) (.sib 0 (some 5) 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f53 : InstrSpec 0x107460 [0x88, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x107460 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x107460 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x107460 7 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107460 7 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m8_r8_effect_step 0x107460 1 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x107467 [0x0F, 0xB6, 0x4C, 0x24, 0x78] (LoadPre 0x107467 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107467 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x107467 5 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107467 5 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (movzx_r32_m8_effect_step 0x107467 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f55 : InstrSpec 0x10746c [0x32, 0x4C, 0x28, 0x0F] (LoadPre 0x10746c (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xf)) s (0x10746c + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10746c 4 1 (.sib 0 (some 5) 0 (.d8 0xf)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10746c 4 1 (.sib 0 (some 5) 0 (.d8 0xf))).toInstrSpec (xor_r8_m8_effect_step 0x10746c 1 (by decide) (.sib 0 (some 5) 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f56 : InstrSpec 0x107470 [0x88, 0x4C, 0x24, 0x78] (StorePre 0x107470 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107470 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107470 4 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107470 4 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m8_r8_effect_step 0x107470 1 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f57 : InstrSpec 0x107474 [0x0F, 0xB6, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x107474 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107474 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107474 8 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107474 8 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (movzx_r32_m8_effect_step 0x107474 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f58 : InstrSpec 0x10747c [0x32, 0x4C, 0x28, 0x10] (LoadPre 0x10747c (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x10)) s (0x10747c + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10747c 4 1 (.sib 0 (some 5) 0 (.d8 0x10)))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10747c 4 1 (.sib 0 (some 5) 0 (.d8 0x10))).toInstrSpec (xor_r8_m8_effect_step 0x10747c 1 (by decide) (.sib 0 (some 5) 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f59 : InstrSpec 0x107480 [0x88, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x107480 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107480 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x107480 7 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107480 7 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m8_r8_effect_step 0x107480 1 (by decide) (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f40 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 120), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10741e) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.exec (n := 122) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 120), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107423) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f42 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107428) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.exec (n := 125) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10742d) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f44 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 77), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107432) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.exec (n := 128) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 77), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107437) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f46 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10743c) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.exec (n := 131) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107441) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f48 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 91), (1, 132), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107449) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f49 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 91), (1, 134), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10744d) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.exec (n := 136) (ρ' := [(0, 91), (1, 134), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107454) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f51 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 91), (1, 137), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10745c) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f52 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 91), (1, 139), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107460) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.exec (n := 141) (ρ' := [(0, 91), (1, 139), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107467) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f54 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 91), (1, 142), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10746c) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f55 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 91), (1, 144), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107470) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.exec (n := 146) (ρ' := [(0, 91), (1, 144), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107474) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f57 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 91), (1, 147), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10747c) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f58 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 91), (1, 149), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107480) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.exec (n := 151) (ρ' := [(0, 91), (1, 149), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 126), (13, 129), (14, 120), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107487) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107315_3 code

theorem rest_l107315_1 [Bindings] (code : CodeMap) :
    Rest (n := 90) code lifted (codeRange 0x107315 bytes_l107315) [(0, 88), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]
      293 0x1073b7 bytes_l107315_1 b_l107315_1 := by
  have f20 : InstrSpec 0x1073b7 [0x88, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x1073b7 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1073b7 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1073b7 7 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1073b7 7 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m8_r8_effect_step 0x1073b7 0 (by decide) (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x1073be [0x48, 0x8B, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00] (LoadPre 0x1073be (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x1073be + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1073be 0 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1073be 0 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x1073be 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x1073c6 [0x32, 0x0C, 0x28] (LoadPre 0x1073c6 (fun s => AddrMode.addr (.sib 0 (some 5) 0 .none) s (0x1073c6 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1073c6 3 1 (.sib 0 (some 5) 0 .none))
      [.gpr 1, .gpr 0, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1073c6 3 1 (.sib 0 (some 5) 0 .none)).toInstrSpec (xor_r8_m8_effect_step 0x1073c6 1 (by decide) (.sib 0 (some 5) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x1073c9 [0x88, 0x4C, 0x24, 0x77] (StorePre 0x1073c9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x77)) s (0x1073c9 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1073c9 4 1 (.sib 4 none 0 (.d8 0x77)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1073c9 4 1 (.sib 4 none 0 (.d8 0x77))).toInstrSpec (mov_m8_r8_effect_step 0x1073c9 1 (by decide) (.sib 4 none 0 (.d8 0x77)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x1073cd [0x32, 0x54, 0x28, 0x01] (LoadPre 0x1073cd (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1)) s (0x1073cd + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1073cd 4 2 (.sib 0 (some 5) 0 (.d8 0x1)))
      [.gpr 2, .gpr 0, .gpr 5] [] [.reg 2, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1073cd 4 2 (.sib 0 (some 5) 0 (.d8 0x1))).toInstrSpec (xor_r8_m8_effect_step 0x1073cd 2 (by decide) (.sib 0 (some 5) 0 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x1073d1 [0x88, 0x54, 0x24, 0x76] (StorePre 0x1073d1 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x1073d1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1073d1 4 2 (.sib 4 none 0 (.d8 0x76)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1073d1 4 2 (.sib 4 none 0 (.d8 0x76))).toInstrSpec (mov_m8_r8_effect_step 0x1073d1 2 (by decide) (.sib 4 none 0 (.d8 0x76)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x1073d5 [0x40, 0x32, 0x74, 0x28, 0x02] (LoadPre 0x1073d5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2)) s (0x1073d5 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1073d5 5 6 (.sib 0 (some 5) 0 (.d8 0x2)))
      [.gpr 6, .gpr 0, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1073d5 5 6 (.sib 0 (some 5) 0 (.d8 0x2))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1073d5 0x40 (by decide) 6 (.sib 0 (some 5) 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x1073da [0x40, 0x88, 0x74, 0x24, 0x75] (StorePre 0x1073da 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x75)) s (0x1073da + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1073da 5 6 (.sib 4 none 0 (.d8 0x75)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1073da 5 6 (.sib 4 none 0 (.d8 0x75))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1073da 0x40 (by decide) 6 (.sib 4 none 0 (.d8 0x75)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x1073df [0x40, 0x32, 0x7C, 0x28, 0x03] (LoadPre 0x1073df (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3)) s (0x1073df + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1073df 5 7 (.sib 0 (some 5) 0 (.d8 0x3)))
      [.gpr 7, .gpr 0, .gpr 5] [] [.reg 7, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1073df 5 7 (.sib 0 (some 5) 0 (.d8 0x3))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1073df 0x40 (by decide) 7 (.sib 0 (some 5) 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x1073e4 [0x40, 0x88, 0x7C, 0x24, 0x74] (StorePre 0x1073e4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x1073e4 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1073e4 5 7 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1073e4 5 7 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1073e4 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x1073e9 [0x44, 0x32, 0x44, 0x28, 0x04] (LoadPre 0x1073e9 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x4)) s (0x1073e9 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1073e9 5 8 (.sib 0 (some 5) 0 (.d8 0x4)))
      [.gpr 8, .gpr 0, .gpr 5] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1073e9 5 8 (.sib 0 (some 5) 0 (.d8 0x4))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1073e9 0x44 (by decide) 0 (.sib 0 (some 5) 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x1073ee [0x44, 0x88, 0x44, 0x24, 0x73] (StorePre 0x1073ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x73)) s (0x1073ee + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1073ee 5 8 (.sib 4 none 0 (.d8 0x73)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1073ee 5 8 (.sib 4 none 0 (.d8 0x73))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1073ee 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x73)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x1073f3 [0x44, 0x32, 0x4C, 0x28, 0x05] (LoadPre 0x1073f3 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x5)) s (0x1073f3 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1073f3 5 9 (.sib 0 (some 5) 0 (.d8 0x5)))
      [.gpr 9, .gpr 0, .gpr 5] [] [.reg 9, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1073f3 5 9 (.sib 0 (some 5) 0 (.d8 0x5))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1073f3 0x44 (by decide) 1 (.sib 0 (some 5) 0 (.d8 0x5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x1073f8 [0x44, 0x88, 0x4C, 0x24, 0x72] (StorePre 0x1073f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x1073f8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1073f8 5 9 (.sib 4 none 0 (.d8 0x72)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1073f8 5 9 (.sib 4 none 0 (.d8 0x72))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1073f8 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x72)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x1073fd [0x44, 0x32, 0x54, 0x28, 0x06] (LoadPre 0x1073fd (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x6)) s (0x1073fd + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1073fd 5 10 (.sib 0 (some 5) 0 (.d8 0x6)))
      [.gpr 10, .gpr 0, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1073fd 5 10 (.sib 0 (some 5) 0 (.d8 0x6))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1073fd 0x44 (by decide) 2 (.sib 0 (some 5) 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x107402 [0x44, 0x88, 0x54, 0x24, 0x71] (StorePre 0x107402 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x71)) s (0x107402 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107402 5 10 (.sib 4 none 0 (.d8 0x71)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107402 5 10 (.sib 4 none 0 (.d8 0x71))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107402 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x71)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x107407 [0x44, 0x32, 0x5C, 0x28, 0x07] (LoadPre 0x107407 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x7)) s (0x107407 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x107407 5 11 (.sib 0 (some 5) 0 (.d8 0x7)))
      [.gpr 11, .gpr 0, .gpr 5] [] [.reg 11, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x107407 5 11 (.sib 0 (some 5) 0 (.d8 0x7))).toInstrSpec (xor_r8_m8_rex_effect_step 0x107407 0x44 (by decide) 3 (.sib 0 (some 5) 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x10740c [0x44, 0x88, 0x5C, 0x24, 0x70] (StorePre 0x10740c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10740c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10740c 5 11 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10740c 5 11 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10740c 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x107411 [0x32, 0x5C, 0x28, 0x08] (LoadPre 0x107411 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x8)) s (0x107411 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x107411 4 3 (.sib 0 (some 5) 0 (.d8 0x8)))
      [.gpr 3, .gpr 0, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x107411 4 3 (.sib 0 (some 5) 0 (.d8 0x8))).toInstrSpec (xor_r8_m8_effect_step 0x107411 3 (by decide) (.sib 0 (some 5) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x107415 [0x88, 0x5C, 0x24, 0x6F] (StorePre 0x107415 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6f)) s (0x107415 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107415 4 3 (.sib 4 none 0 (.d8 0x6f)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107415 4 3 (.sib 4 none 0 (.d8 0x6f))).toInstrSpec (mov_m8_r8_effect_step 0x107415 3 (by decide) (.sib 4 none 0 (.d8 0x6f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 88), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073be) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 91), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073c6) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 91), (1, 93), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073c9) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 91), (1, 93), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073cd) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f24 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073d1) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073d5) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f26 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073da) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073df) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f28 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073e4) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073e9) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f30 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073ee) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073f3) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f32 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073f8) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.exec (n := 110) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073fd) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f34 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107402) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.exec (n := 113) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107407) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f36 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10740c) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.exec (n := 116) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 69), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107411) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f38 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107415) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.exec (n := 119) (ρ' := [(0, 91), (1, 93), (2, 96), (3, 117), (4, 4), (5, 5), (6, 99), (7, 102), (8, 105), (9, 108), (10, 111), (11, 114), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107419) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107315_2 code

theorem rest_l107315 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107315 bytes_l107315) (entryMap (live .l107315))
      313 0x107315 bytes_l107315 b_l107315 := by
  have f0 : InstrSpec 0x107315 [0x0F, 0xB6, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x107315 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x107315 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107315 8 1 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107315 8 1 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (movzx_r32_m8_effect_step 0x107315 1 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10731d [0x0F, 0xB6, 0x94, 0x24, 0x99, 0x00, 0x00, 0x00] (LoadPre 0x10731d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x99)) s (0x10731d + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10731d 8 2 (.sib 4 none 0 (.d32 0x99)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x10731d 8 2 (.sib 4 none 0 (.d32 0x99))).toInstrSpec (movzx_r32_m8_effect_step 0x10731d 2 (.sib 4 none 0 (.d32 0x99)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x107325 [0x0F, 0xB6, 0xB4, 0x24, 0x9A, 0x00, 0x00, 0x00] (LoadPre 0x107325 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9a)) s (0x107325 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107325 8 6 (.sib 4 none 0 (.d32 0x9a)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x107325 8 6 (.sib 4 none 0 (.d32 0x9a))).toInstrSpec (movzx_r32_m8_effect_step 0x107325 6 (.sib 4 none 0 (.d32 0x9a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10732d [0x0F, 0xB6, 0xBC, 0x24, 0x9B, 0x00, 0x00, 0x00] (LoadPre 0x10732d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9b)) s (0x10732d + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10732d 8 7 (.sib 4 none 0 (.d32 0x9b)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x10732d 8 7 (.sib 4 none 0 (.d32 0x9b))).toInstrSpec (movzx_r32_m8_effect_step 0x10732d 7 (.sib 4 none 0 (.d32 0x9b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x107335 [0x44, 0x0F, 0xB6, 0x84, 0x24, 0x9C, 0x00, 0x00, 0x00] (LoadPre 0x107335 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x107335 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107335 9 8 (.sib 4 none 0 (.d32 0x9c)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x107335 9 8 (.sib 4 none 0 (.d32 0x9c))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107335 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0x9c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10733e [0x44, 0x0F, 0xB6, 0x8C, 0x24, 0x9D, 0x00, 0x00, 0x00] (LoadPre 0x10733e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9d)) s (0x10733e + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x10733e 9 9 (.sib 4 none 0 (.d32 0x9d)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x10733e 9 9 (.sib 4 none 0 (.d32 0x9d))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10733e 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0x9d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x107347 [0x44, 0x0F, 0xB6, 0x94, 0x24, 0x9E, 0x00, 0x00, 0x00] (LoadPre 0x107347 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9e)) s (0x107347 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107347 9 10 (.sib 4 none 0 (.d32 0x9e)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x107347 9 10 (.sib 4 none 0 (.d32 0x9e))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107347 0x44 (by decide) 2 (.sib 4 none 0 (.d32 0x9e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x107350 [0x44, 0x0F, 0xB6, 0x9C, 0x24, 0x9F, 0x00, 0x00, 0x00] (LoadPre 0x107350 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x107350 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107350 9 11 (.sib 4 none 0 (.d32 0x9f)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x107350 9 11 (.sib 4 none 0 (.d32 0x9f))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107350 0x44 (by decide) 3 (.sib 4 none 0 (.d32 0x9f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x107359 [0x0F, 0xB6, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x107359 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x107359 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107359 8 3 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x107359 8 3 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (movzx_r32_m8_effect_step 0x107359 3 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x107361 [0x44, 0x0F, 0xB6, 0xB4, 0x24, 0xA1, 0x00, 0x00, 0x00] (LoadPre 0x107361 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa1)) s (0x107361 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107361 9 14 (.sib 4 none 0 (.d32 0xa1)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x107361 9 14 (.sib 4 none 0 (.d32 0xa1))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107361 0x44 (by decide) 6 (.sib 4 none 0 (.d32 0xa1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x10736a [0x44, 0x0F, 0xB6, 0xBC, 0x24, 0xA2, 0x00, 0x00, 0x00] (LoadPre 0x10736a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa2)) s (0x10736a + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x10736a 9 15 (.sib 4 none 0 (.d32 0xa2)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x10736a 9 15 (.sib 4 none 0 (.d32 0xa2))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10736a 0x44 (by decide) 7 (.sib 4 none 0 (.d32 0xa2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x107373 [0x44, 0x0F, 0xB6, 0xA4, 0x24, 0xA3, 0x00, 0x00, 0x00] (LoadPre 0x107373 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa3)) s (0x107373 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107373 9 12 (.sib 4 none 0 (.d32 0xa3)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x107373 9 12 (.sib 4 none 0 (.d32 0xa3))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107373 0x44 (by decide) 4 (.sib 4 none 0 (.d32 0xa3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x10737c [0x44, 0x0F, 0xB6, 0xAC, 0x24, 0xA4, 0x00, 0x00, 0x00] (LoadPre 0x10737c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x10737c + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x10737c 9 13 (.sib 4 none 0 (.d32 0xa4)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x10737c 9 13 (.sib 4 none 0 (.d32 0xa4))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10737c 0x44 (by decide) 5 (.sib 4 none 0 (.d32 0xa4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x107385 [0x0F, 0xB6, 0x84, 0x24, 0xA5, 0x00, 0x00, 0x00] (LoadPre 0x107385 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa5)) s (0x107385 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107385 8 0 (.sib 4 none 0 (.d32 0xa5)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x107385 8 0 (.sib 4 none 0 (.d32 0xa5))).toInstrSpec (movzx_r32_m8_effect_step 0x107385 0 (.sib 4 none 0 (.d32 0xa5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10738d [0x88, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x10738d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10738d + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10738d 7 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10738d 7 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m8_r8_effect_step 0x10738d 0 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x107394 [0x0F, 0xB6, 0x84, 0x24, 0xA6, 0x00, 0x00, 0x00] (LoadPre 0x107394 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa6)) s (0x107394 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107394 8 0 (.sib 4 none 0 (.d32 0xa6)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x107394 8 0 (.sib 4 none 0 (.d32 0xa6))).toInstrSpec (movzx_r32_m8_effect_step 0x107394 0 (.sib 4 none 0 (.d32 0xa6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10739c [0x88, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x10739c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10739c + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10739c 7 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10739c 7 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m8_r8_effect_step 0x10739c 0 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x1073a3 [0x0F, 0xB6, 0x84, 0x24, 0xA7, 0x00, 0x00, 0x00] (LoadPre 0x1073a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa7)) s (0x1073a3 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1073a3 8 0 (.sib 4 none 0 (.d32 0xa7)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1073a3 8 0 (.sib 4 none 0 (.d32 0xa7))).toInstrSpec (movzx_r32_m8_effect_step 0x1073a3 0 (.sib 4 none 0 (.d32 0xa7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x1073ab [0x88, 0x44, 0x24, 0x78] (StorePre 0x1073ab 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1073ab + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1073ab 4 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1073ab 4 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m8_r8_effect_step 0x1073ab 0 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1073af [0x0F, 0xB6, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x1073af (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1073af + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1073af 8 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1073af 8 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (movzx_r32_m8_effect_step 0x1073af 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10731d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 55), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107325) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (2, 55), (4, 4), (5, 5), (6, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10732d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 53), (2, 55), (4, 4), (5, 5), (6, 57), (7, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107335) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 53), (2, 55), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10733e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 53), (2, 55), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107347) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 53), (2, 55), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107350) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 53), (2, 55), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107359) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107361) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (14, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10736a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107373) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10737c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107385) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10738d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 79), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107394) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 82), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10739c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 82), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073a3) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073ab) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 85), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073af) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 88), (1, 53), (2, 55), (3, 69), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 63), (10, 65), (11, 67), (12, 75), (13, 77), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073b7) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107315_1 code

theorem block_l107315 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107315 :=
  Rest.liftedBlock (rest_l107315 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107315 x hx)

theorem rest_l107a08_2 [Bindings] (code : CodeMap) :
    Rest (n := 108) code lifted (codeRange 0x107a08 bytes_l107a08) [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x107afb bytes_l107a08_2 b_l107a08_2 := by
  have f40 : InstrSpec 0x107afb [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107afb) (movR32Imm32Effect 0x107afb 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x107afb 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x107afb 0xbe (by decide) 0x8) pre_rip
  have f41 : InstrSpec 0x107b00 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x107b00) (leaR64Effect 0x107b00 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x107b00 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x107b00 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x107b05 [0x48, 0x8D, 0x94, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x107b05) (leaR64Effect 0x107b05 2 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x107b05 2 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x107b05 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x107b0d [0xE8, 0x7E, 0x2B, 0x00, 0x00] (PushPre 0x107b0d 5) (callEffect (fun _ => 0x10a690) 0x107b12)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107b0d 0x10a690 0x107b12).toInstrSpec (call_rel32_effect_step 0x107b0d 0x2b7e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f40 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 108), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b00) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f41 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 108), (7, 110), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b05) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f42 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 93), (1, 57), (2, 112), (3, 3), (4, 4), (5, 5), (6, 108), (7, 110), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b0d) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f43 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 93), (1, 57), (2, 112), (3, 3), (4, 114), (5, 5), (6, 108), (7, 110), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a690) f43 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 116) (by decide) (by decide) rfl rfl

theorem rest_l107a08_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x107a08 bytes_l107a08) [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      24 0x107a73 bytes_l107a08_1 b_l107a08_1 := by
  have f20 : InstrSpec 0x107a73 [0x89, 0x94, 0x24, 0x24, 0x01, 0x00, 0x00] (StorePre 0x107a73 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x124)) s (0x107a73 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a73 2 (.sib 4 none 0 (.d32 0x124)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107a73 2 (.sib 4 none 0 (.d32 0x124))).toInstrSpec (mov_m32_r32_low_effect_step 0x107a73 2 (.sib 4 none 0 (.d32 0x124)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x107a7a [0x89, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00] (StorePre 0x107a7a 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x107a7a + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a7a 6 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107a7a 6 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_m32_r32_low_effect_step 0x107a7a 6 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x107a81 [0x44, 0x89, 0x84, 0x24, 0x2C, 0x01, 0x00, 0x00] (StorePre 0x107a81 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x12c)) s (0x107a81 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x107a81 8 (.sib 4 none 0 (.d32 0x12c)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x107a81 8 (.sib 4 none 0 (.d32 0x12c))).toInstrSpec (mov_m32_r32_effect_step 0x107a81 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0x12c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x107a89 [0x01, 0xC7] (fun s => s.RIP = 0x107a89) (addR32R32Effect 0x107a89 2 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (addR32R32Effect_footprint 0x107a89 2 7 0).toInstrSpec (add_r32_r32_effect_step 0x107a89 0xc7 (by decide)) pre_rip
  have f24 : InstrSpec 0x107a8b [0x83, 0xC7, 0x03] (fun s => s.RIP = 0x107a8b) (addR32Imm8Effect 0x107a8b 3 7 0x3)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR32Imm8Effect_footprint 0x107a8b 3 7 0x3).toInstrSpec (add_r32_imm8_effect_step 0x107a8b 0xc7 0x3 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x107a8e [0x0F, 0xCF] (fun s => s.RIP = 0x107a8e) (bswapR32Effect 0x107a8e 2 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (bswapR32Effect_footprint 0x107a8e 2 7).toInstrSpec (bswap_r32_effect_step 0x107a8e 0xcf (by decide)) pre_rip
  have f26 : InstrSpec 0x107a90 [0x83, 0xC0, 0x04] (fun s => s.RIP = 0x107a90) (addR32Imm8Effect 0x107a90 3 0 0x4)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32Imm8Effect_footprint 0x107a90 3 0 0x4).toInstrSpec (add_r32_imm8_effect_step 0x107a90 0xc0 0x4 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x107a93 [0x41, 0x89, 0x41, 0x10] (StorePre 0x107a93 4 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x107a93 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x107a93 0 (.base 9 (.d8 0x10)))
      [.gpr 0, .gpr 9] [] [.rip] :=
    (movM32R32Effect_footprint 0x107a93 0 (.base 9 (.d8 0x10))).toInstrSpec (mov_m32_r32_effect_step 0x107a93 0x41 (by decide) 0 (.base 9 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x107a97 [0x89, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00] (StorePre 0x107a97 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x107a97 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a97 1 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107a97 1 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_m32_r32_low_effect_step 0x107a97 1 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x107a9e [0x89, 0x94, 0x24, 0x34, 0x01, 0x00, 0x00] (StorePre 0x107a9e 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x134)) s (0x107a9e + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a9e 2 (.sib 4 none 0 (.d32 0x134)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107a9e 2 (.sib 4 none 0 (.d32 0x134))).toInstrSpec (mov_m32_r32_low_effect_step 0x107a9e 2 (.sib 4 none 0 (.d32 0x134)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x107aa5 [0x89, 0xB4, 0x24, 0x38, 0x01, 0x00, 0x00] (StorePre 0x107aa5 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x107aa5 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107aa5 6 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107aa5 6 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_m32_r32_low_effect_step 0x107aa5 6 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x107aac [0x89, 0xBC, 0x24, 0x3C, 0x01, 0x00, 0x00] (StorePre 0x107aac 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x13c)) s (0x107aac + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107aac 7 (.sib 4 none 0 (.d32 0x13c)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107aac 7 (.sib 4 none 0 (.d32 0x13c))).toInstrSpec (mov_m32_r32_low_effect_step 0x107aac 7 (.sib 4 none 0 (.d32 0x13c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x107ab3 [0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107ab3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107ab3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107ab3 (.sib 4 none 0 (.d8 0x40)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107ab3 (.sib 4 none 0 (.d8 0x40)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107ab3 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x107abc [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107abc 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107abc + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107abc (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107abc (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107abc 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x107ac5 [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107ac5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107ac5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107ac5 (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107ac5 (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107ac5 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x107ace [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107ace 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107ace + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107ace (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107ace (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107ace 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x107ad7 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107ad7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107ad7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107ad7 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107ad7 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107ad7 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x107ae0 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107ae0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107ae0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107ae0 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107ae0 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107ae0 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x107ae9 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107ae9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107ae9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107ae9 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107ae9 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107ae9 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x107af2 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107af2 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107af2 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107af2 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107af2 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107af2 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a7a) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a81) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a89) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f23 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 87), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a8b) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f24 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 89), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a8e) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f25 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a90) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f26 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a93) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a97) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a9e) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107aa5) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107aac) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ab3) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107abc) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ac5) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.exec (n := 102) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ace) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 103) (RestInside.exec (n := 103) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ad7) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ae0) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.exec (n := 105) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ae9) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107af2) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 93), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107afb) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107a08_2 code

theorem rest_l107a08 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107a08 bytes_l107a08) (entryMap (live .l107a08))
      44 0x107a08 bytes_l107a08 b_l107a08 := by
  have f0 : InstrSpec 0x107a08 [0x41, 0x8B, 0x41, 0x10] (LoadPre 0x107a08 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x107a08 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x107a08 0 (.base 9 (.d8 0x10)))
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR32M32Effect_footprint 0x107a08 0 (.base 9 (.d8 0x10))).toInstrSpec (mov_r32_m32_effect_step 0x107a08 0x41 (by decide) 0 (.base 9 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107a0c [0x41, 0x8B, 0x79, 0x0C] (LoadPre 0x107a0c (fun s => AddrMode.addr (.base 9 (.d8 0xc)) s (0x107a0c + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x107a0c 7 (.base 9 (.d8 0xc)))
      [.gpr 9] [] [.reg 7, .rip] :=
    (movR32M32Effect_footprint 0x107a0c 7 (.base 9 (.d8 0xc))).toInstrSpec (mov_r32_m32_effect_step 0x107a0c 0x41 (by decide) 7 (.base 9 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x107a10 [0x41, 0x8B, 0x09] (LoadPre 0x107a10 (fun s => AddrMode.addr (.base 9 .none) s (0x107a10 + BitVec.ofNat 64 3)) 4) (movR32M32Effect 0x107a10 1 (.base 9 .none))
      [.gpr 9] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x107a10 1 (.base 9 .none)).toInstrSpec (mov_r32_m32_effect_step 0x107a10 0x41 (by decide) 1 (.base 9 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x107a13 [0x41, 0x8B, 0x51, 0x04] (LoadPre 0x107a13 (fun s => AddrMode.addr (.base 9 (.d8 0x4)) s (0x107a13 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x107a13 2 (.base 9 (.d8 0x4)))
      [.gpr 9] [] [.reg 2, .rip] :=
    (movR32M32Effect_footprint 0x107a13 2 (.base 9 (.d8 0x4))).toInstrSpec (mov_r32_m32_effect_step 0x107a13 0x41 (by decide) 2 (.base 9 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x107a17 [0x41, 0x8B, 0x71, 0x08] (LoadPre 0x107a17 (fun s => AddrMode.addr (.base 9 (.d8 0x8)) s (0x107a17 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x107a17 6 (.base 9 (.d8 0x8)))
      [.gpr 9] [] [.reg 6, .rip] :=
    (movR32M32Effect_footprint 0x107a17 6 (.base 9 (.d8 0x8))).toInstrSpec (mov_r32_m32_effect_step 0x107a17 0x41 (by decide) 6 (.base 9 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x107a1b [0x44, 0x8D, 0x04, 0x07] (fun s => s.RIP = 0x107a1b) (leaR32Effect 0x107a1b 4 8 (.sib 7 (some 0) 0 .none))
      [.gpr 7, .gpr 0] [] [.reg 8, .rip] :=
    (leaR32Effect_footprint 0x107a1b 4 8 (.sib 7 (some 0) 0 .none)).toInstrSpec (lea_r32_rex_effect_step 0x107a1b 0x44 (by decide) 0 (.sib 7 (some 0) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x107a1f [0x41, 0x0F, 0xC8] (fun s => s.RIP = 0x107a1f) (bswapR32Effect 0x107a1f 3 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (bswapR32Effect_footprint 0x107a1f 3 8).toInstrSpec (bswap_r32_rex_effect_step 0x107a1f 0x41 (by decide) 0xc8 (by decide)) pre_rip
  have f7 : InstrSpec 0x107a22 [0x89, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x107a22 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x107a22 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a22 1 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107a22 1 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m32_r32_low_effect_step 0x107a22 1 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x107a29 [0x89, 0x94, 0x24, 0x04, 0x01, 0x00, 0x00] (StorePre 0x107a29 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x104)) s (0x107a29 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a29 2 (.sib 4 none 0 (.d32 0x104)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107a29 2 (.sib 4 none 0 (.d32 0x104))).toInstrSpec (mov_m32_r32_low_effect_step 0x107a29 2 (.sib 4 none 0 (.d32 0x104)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x107a30 [0x89, 0xB4, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x107a30 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x107a30 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a30 6 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107a30 6 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m32_r32_low_effect_step 0x107a30 6 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x107a37 [0x44, 0x89, 0x84, 0x24, 0x0C, 0x01, 0x00, 0x00] (StorePre 0x107a37 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10c)) s (0x107a37 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x107a37 8 (.sib 4 none 0 (.d32 0x10c)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x107a37 8 (.sib 4 none 0 (.d32 0x10c))).toInstrSpec (mov_m32_r32_effect_step 0x107a37 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0x10c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x107a3f [0x44, 0x8D, 0x44, 0x07, 0x01] (fun s => s.RIP = 0x107a3f) (leaR32Effect 0x107a3f 5 8 (.sib 7 (some 0) 0 (.d8 0x1)))
      [.gpr 7, .gpr 0] [] [.reg 8, .rip] :=
    (leaR32Effect_footprint 0x107a3f 5 8 (.sib 7 (some 0) 0 (.d8 0x1))).toInstrSpec (lea_r32_rex_effect_step 0x107a3f 0x44 (by decide) 0 (.sib 7 (some 0) 0 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x107a44 [0x41, 0x0F, 0xC8] (fun s => s.RIP = 0x107a44) (bswapR32Effect 0x107a44 3 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (bswapR32Effect_footprint 0x107a44 3 8).toInstrSpec (bswap_r32_rex_effect_step 0x107a44 0x41 (by decide) 0xc8 (by decide)) pre_rip
  have f13 : InstrSpec 0x107a47 [0x89, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x107a47 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x107a47 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a47 1 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107a47 1 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m32_r32_low_effect_step 0x107a47 1 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x107a4e [0x89, 0x94, 0x24, 0x14, 0x01, 0x00, 0x00] (StorePre 0x107a4e 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x114)) s (0x107a4e + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a4e 2 (.sib 4 none 0 (.d32 0x114)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107a4e 2 (.sib 4 none 0 (.d32 0x114))).toInstrSpec (mov_m32_r32_low_effect_step 0x107a4e 2 (.sib 4 none 0 (.d32 0x114)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x107a55 [0x89, 0xB4, 0x24, 0x18, 0x01, 0x00, 0x00] (StorePre 0x107a55 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x107a55 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a55 6 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107a55 6 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_m32_r32_low_effect_step 0x107a55 6 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x107a5c [0x44, 0x89, 0x84, 0x24, 0x1C, 0x01, 0x00, 0x00] (StorePre 0x107a5c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11c)) s (0x107a5c + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x107a5c 8 (.sib 4 none 0 (.d32 0x11c)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x107a5c 8 (.sib 4 none 0 (.d32 0x11c))).toInstrSpec (mov_m32_r32_effect_step 0x107a5c 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0x11c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x107a64 [0x44, 0x8D, 0x44, 0x07, 0x02] (fun s => s.RIP = 0x107a64) (leaR32Effect 0x107a64 5 8 (.sib 7 (some 0) 0 (.d8 0x2)))
      [.gpr 7, .gpr 0] [] [.reg 8, .rip] :=
    (leaR32Effect_footprint 0x107a64 5 8 (.sib 7 (some 0) 0 (.d8 0x2))).toInstrSpec (lea_r32_rex_effect_step 0x107a64 0x44 (by decide) 0 (.sib 7 (some 0) 0 (.d8 0x2)) (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x107a69 [0x41, 0x0F, 0xC8] (fun s => s.RIP = 0x107a69) (bswapR32Effect 0x107a69 3 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (bswapR32Effect_footprint 0x107a69 3 8).toInstrSpec (bswap_r32_rex_effect_step 0x107a69 0x41 (by decide) 0xc8 (by decide)) pre_rip
  have f19 : InstrSpec 0x107a6c [0x89, 0x8C, 0x24, 0x20, 0x01, 0x00, 0x00] (StorePre 0x107a6c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x107a6c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a6c 1 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107a6c 1 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_m32_r32_low_effect_step 0x107a6c 1 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a0c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a10) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a13) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a17) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a1b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a1f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 65), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a22) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 65), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a29) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 65), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a30) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 65), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a37) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 65), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a3f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 71), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a44) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 73), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a47) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 73), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a4e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 73), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a55) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 73), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a5c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 73), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a64) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 79), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a69) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a6c) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 55), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a73) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107a08_1 code

theorem block_l107a08 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107a08 :=
  Rest.liftedBlock (rest_l107a08 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107a08 x hx)

theorem rest_l107b12 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107b12 bytes_l107b12) (entryMap (live .l107b12))
      17 0x107b12 bytes_l107b12 b_l107b12 := by
  have f0 : InstrSpec 0x107b12 [0x48, 0x8B, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00] (LoadPre 0x107b12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x107b12 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107b12 0 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107b12 0 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (mov_r64_m64_effect_step 0x107b12 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107b1a [0x48, 0x31, 0x44, 0x24, 0x08] (StorePre 0x107b1a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107b1a + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107b1a 5 64 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x107b1a 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (xor_m64_r64_effect_step 0x107b1a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x107b1f [0x48, 0x8B, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00] (LoadPre 0x107b1f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x107b1f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107b1f 0 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107b1f 0 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (mov_r64_m64_effect_step 0x107b1f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x107b27 [0x48, 0x31, 0x44, 0x24, 0x10] (StorePre 0x107b27 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107b27 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107b27 5 64 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x107b27 5 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (xor_m64_r64_effect_step 0x107b27 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x107b2c [0x48, 0x8B, 0x84, 0x24, 0x68, 0x01, 0x00, 0x00] (LoadPre 0x107b2c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x107b2c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107b2c 0 (.sib 4 none 0 (.d32 0x168)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107b2c 0 (.sib 4 none 0 (.d32 0x168))).toInstrSpec (mov_r64_m64_effect_step 0x107b2c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x168)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x107b34 [0x48, 0x31, 0x44, 0x24, 0x18] (StorePre 0x107b34 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107b34 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107b34 5 64 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x107b34 5 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (xor_m64_r64_effect_step 0x107b34 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x107b39 [0x48, 0x8B, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00] (LoadPre 0x107b39 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x107b39 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107b39 0 (.sib 4 none 0 (.d32 0x170)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107b39 0 (.sib 4 none 0 (.d32 0x170))).toInstrSpec (mov_r64_m64_effect_step 0x107b39 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x107b41 [0x48, 0x31, 0x44, 0x24, 0x20] (StorePre 0x107b41 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107b41 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107b41 5 64 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x107b41 5 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (xor_m64_r64_effect_step 0x107b41 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x107b46 [0x48, 0x8B, 0x84, 0x24, 0x78, 0x01, 0x00, 0x00] (LoadPre 0x107b46 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x107b46 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107b46 0 (.sib 4 none 0 (.d32 0x178)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107b46 0 (.sib 4 none 0 (.d32 0x178))).toInstrSpec (mov_r64_m64_effect_step 0x107b46 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x178)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x107b4e [0x48, 0x31, 0x44, 0x24, 0x28] (StorePre 0x107b4e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107b4e + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107b4e 5 64 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x107b4e 5 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (xor_m64_r64_effect_step 0x107b4e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x107b53 [0x48, 0x8B, 0x84, 0x24, 0x80, 0x01, 0x00, 0x00] (LoadPre 0x107b53 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x107b53 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107b53 0 (.sib 4 none 0 (.d32 0x180)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107b53 0 (.sib 4 none 0 (.d32 0x180))).toInstrSpec (mov_r64_m64_effect_step 0x107b53 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x180)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x107b5b [0x48, 0x31, 0x44, 0x24, 0x30] (StorePre 0x107b5b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107b5b + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107b5b 5 64 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x107b5b 5 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (xor_m64_r64_effect_step 0x107b5b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x107b60 [0x48, 0x8B, 0x84, 0x24, 0x88, 0x01, 0x00, 0x00] (LoadPre 0x107b60 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x107b60 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107b60 0 (.sib 4 none 0 (.d32 0x188)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107b60 0 (.sib 4 none 0 (.d32 0x188))).toInstrSpec (mov_r64_m64_effect_step 0x107b60 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x188)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x107b68 [0x48, 0x31, 0x44, 0x24, 0x38] (StorePre 0x107b68 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107b68 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107b68 5 64 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x107b68 5 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (xor_m64_r64_effect_step 0x107b68 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x107b6d [0x4C, 0x8B, 0x74, 0x24, 0x40] (LoadPre 0x107b6d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107b6d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b6d 14 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x107b6d 14 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x107b6d 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x107b72 [0x31, 0xED] (fun s => s.RIP = 0x107b72) (xorR32R32Effect 0x107b72 2 5 5)
      [.gpr 5, .gpr 5] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x107b72 2 5 5).toInstrSpec (xor_r32_r32_effect_step 0x107b72 0xed (by decide)) pre_rip
  have f16 : InstrSpec 0x107b74 [0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107b74) (fun _ => nopEffect 0x107b74 12)
      [] [] [.rip] :=
    (nopEffect_footprint 0x107b74 12).toInstrSpec (nop_m_effect_step 0x107b74 [0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b1a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b1f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b27) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b2c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b34) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b39) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b41) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b46) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b4e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b53) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b5b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b60) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b68) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b6d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 71), (4, 4), (5, 5), (12, 12), (13, 13), (14, 74), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b72) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 71), (4, 4), (5, 76), (12, 12), (13, 13), (14, 74), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b74) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 71), (4, 4), (5, 76), (12, 12), (13, 13), (14, 74), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b80) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 79) (by decide) rfl

theorem block_l107b12 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107b12 :=
  Rest.liftedBlock (rest_l107b12 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107b12 x hx)

theorem rest_l107b80 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107b80 bytes_l107b80) (entryMap (live .l107b80))
      6 0x107b80 bytes_l107b80 b_l107b80 := by
  have f0 : InstrSpec 0x107b80 [0x4C, 0x33, 0xB4, 0xEC, 0x90, 0x01, 0x00, 0x00] (LoadPre 0x107b80 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x190)) s (0x107b80 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107b80 14 (.sib 4 (some 5) 3 (.d32 0x190)))
      [.gpr 14, .gpr 4, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107b80 14 (.sib 4 (some 5) 3 (.d32 0x190))).toInstrSpec (xor_r64_m64_effect_step 0x107b80 0x4c (by decide) 6 (.sib 4 (some 5) 3 (.d32 0x190)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107b88 [0x4C, 0x89, 0x74, 0x24, 0x40] (StorePre 0x107b88 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107b88 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107b88 14 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107b88 14 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x107b88 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x107b8d [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107b8d) (movR32Imm32Effect 0x107b8d 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x107b8d 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x107b8d 0xbe (by decide) 0x8) pre_rip
  have f3 : InstrSpec 0x107b92 [0x48, 0x8D, 0x5C, 0x24, 0x08] (fun s => s.RIP = 0x107b92) (leaR64Effect 0x107b92 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x107b92 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x107b92 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x107b97 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x107b97) (movR64R64Effect 0x107b97 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x107b97 7 3).toInstrSpec (mov_r64_r64_effect_step 0x107b97 0x48 0xdf (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x107b9a [0xE8, 0xF1, 0x92, 0xFF, 0xFF] (PushPre 0x107b9a 5) (callEffect (fun _ => 0x100e90) 0x107b9f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107b9a 0x100e90 0x107b9f).toInstrSpec (call_rel32_effect_step 0x107b9a 0xffff92f1 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b88) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(4, 4), (5, 5), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b8d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(4, 4), (5, 5), (6, 56), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b92) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(3, 58), (4, 4), (5, 5), (6, 56), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b97) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 58), (4, 4), (5, 5), (6, 56), (7, 60), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b9a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 58), (4, 62), (5, 5), (6, 56), (7, 60), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e90) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 64) (by decide) (by decide) rfl rfl

theorem block_l107b80 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107b80 :=
  Rest.liftedBlock (rest_l107b80 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107b80 x hx)

theorem rest_l107b9f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107b9f bytes_l107b9f) (entryMap (live .l107b9f))
      2 0x107b9f bytes_l107b9f b_l107b9f := by
  have f0 : InstrSpec 0x107b9f [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x107b9f) (movR64R64Effect 0x107b9f 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x107b9f 7 3).toInstrSpec (mov_r64_r64_effect_step 0x107b9f 0x48 0xdf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x107ba2 [0xE8, 0xF9, 0x86, 0xFF, 0xFF] (PushPre 0x107ba2 5) (callEffect (fun _ => 0x1002a0) 0x107ba7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107ba2 0x1002a0 0x107ba7).toInstrSpec (call_rel32_effect_step 0x107ba2 0xffff86f9 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ba2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002a0) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l107b9f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107b9f :=
  Rest.liftedBlock (rest_l107b9f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107b9f x hx)

theorem rest_l107ba7_1 [Bindings] (code : CodeMap) :
    Rest (n := 87) code lifted (codeRange 0x107ba7 bytes_l107ba7) [(1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x107c20 bytes_l107ba7_1 b_l107ba7_1 := by
  have f20 : InstrSpec 0x107c20 [0x48, 0x89, 0x4C, 0x24, 0x38] (StorePre 0x107c20 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107c20 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107c20 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107c20 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x107c20 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x107c25 [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x107c25 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107c25 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c25 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107c25 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x107c25 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x107c2a [0x48, 0x33, 0x84, 0xEC, 0xD0, 0x01, 0x00, 0x00] (LoadPre 0x107c2a (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1d0)) s (0x107c2a + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107c2a 0 (.sib 4 (some 5) 3 (.d32 0x1d0)))
      [.gpr 0, .gpr 4, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107c2a 0 (.sib 4 (some 5) 3 (.d32 0x1d0))).toInstrSpec (xor_r64_m64_effect_step 0x107c2a 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x107c32 [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x107c32 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107c32 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107c32 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107c32 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x107c32 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x107c37 [0x48, 0x83, 0xFD, 0x40] (fun s => s.RIP = 0x107c37) (cmpR64Imm8Effect 0x107c37 5 0x40)
      [.gpr 5] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x107c37 5 0x40).toInstrSpec (cmp_r64_imm8_effect_step 0x107c37 0x48 0xfd 0x40 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c25) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 88), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c2a) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c32) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c37) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f24 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (19, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c3b) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 95) (jcc_rel32_effect_step 0x107c3b 4 0xfffff52f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l107ba7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107ba7 bytes_l107ba7) (entryMap (live .l107ba7))
      26 0x107ba7 bytes_l107ba7 b_l107ba7 := by
  have f0 : InstrSpec 0x107ba7 [0x4C, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x107ba7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107ba7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107ba7 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x107ba7 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x107ba7 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107bac [0x4C, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x107bac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107bac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107bac 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x107bac 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x107bac 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x107bb1 [0x4C, 0x33, 0x94, 0xEC, 0x98, 0x01, 0x00, 0x00] (LoadPre 0x107bb1 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x198)) s (0x107bb1 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107bb1 10 (.sib 4 (some 5) 3 (.d32 0x198)))
      [.gpr 10, .gpr 4, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107bb1 10 (.sib 4 (some 5) 3 (.d32 0x198))).toInstrSpec (xor_r64_m64_effect_step 0x107bb1 0x4c (by decide) 2 (.sib 4 (some 5) 3 (.d32 0x198)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x107bb9 [0x4C, 0x89, 0x54, 0x24, 0x08] (StorePre 0x107bb9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107bb9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107bb9 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107bb9 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x107bb9 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x107bbe [0x4C, 0x33, 0x8C, 0xEC, 0xA0, 0x01, 0x00, 0x00] (LoadPre 0x107bbe (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1a0)) s (0x107bbe + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107bbe 9 (.sib 4 (some 5) 3 (.d32 0x1a0)))
      [.gpr 9, .gpr 4, .gpr 5] [] [.reg 9, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107bbe 9 (.sib 4 (some 5) 3 (.d32 0x1a0))).toInstrSpec (xor_r64_m64_effect_step 0x107bbe 0x4c (by decide) 1 (.sib 4 (some 5) 3 (.d32 0x1a0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x107bc6 [0x4C, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x107bc6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107bc6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107bc6 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107bc6 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x107bc6 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x107bcb [0x4C, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x107bcb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107bcb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107bcb 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x107bcb 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x107bcb 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x107bd0 [0x4C, 0x33, 0x84, 0xEC, 0xA8, 0x01, 0x00, 0x00] (LoadPre 0x107bd0 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1a8)) s (0x107bd0 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107bd0 8 (.sib 4 (some 5) 3 (.d32 0x1a8)))
      [.gpr 8, .gpr 4, .gpr 5] [] [.reg 8, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107bd0 8 (.sib 4 (some 5) 3 (.d32 0x1a8))).toInstrSpec (xor_r64_m64_effect_step 0x107bd0 0x4c (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x1a8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x107bd8 [0x4C, 0x89, 0x44, 0x24, 0x18] (StorePre 0x107bd8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107bd8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107bd8 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107bd8 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x107bd8 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x107bdd [0x48, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x107bdd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107bdd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107bdd 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x107bdd 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x107bdd 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x107be2 [0x48, 0x33, 0xBC, 0xEC, 0xB0, 0x01, 0x00, 0x00] (LoadPre 0x107be2 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1b0)) s (0x107be2 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107be2 7 (.sib 4 (some 5) 3 (.d32 0x1b0)))
      [.gpr 7, .gpr 4, .gpr 5] [] [.reg 7, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107be2 7 (.sib 4 (some 5) 3 (.d32 0x1b0))).toInstrSpec (xor_r64_m64_effect_step 0x107be2 0x48 (by decide) 7 (.sib 4 (some 5) 3 (.d32 0x1b0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x107bea [0x48, 0x89, 0x7C, 0x24, 0x20] (StorePre 0x107bea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107bea + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107bea 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107bea 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x107bea 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x107bef [0x48, 0x8B, 0x74, 0x24, 0x28] (LoadPre 0x107bef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107bef + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107bef 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x107bef 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x107bef 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x107bf4 [0x48, 0x33, 0xB4, 0xEC, 0xB8, 0x01, 0x00, 0x00] (LoadPre 0x107bf4 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1b8)) s (0x107bf4 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107bf4 6 (.sib 4 (some 5) 3 (.d32 0x1b8)))
      [.gpr 6, .gpr 4, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107bf4 6 (.sib 4 (some 5) 3 (.d32 0x1b8))).toInstrSpec (xor_r64_m64_effect_step 0x107bf4 0x48 (by decide) 6 (.sib 4 (some 5) 3 (.d32 0x1b8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x107bfc [0x48, 0x89, 0x74, 0x24, 0x28] (StorePre 0x107bfc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107bfc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107bfc 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107bfc 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x107bfc 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x107c01 [0x48, 0x8B, 0x54, 0x24, 0x30] (LoadPre 0x107c01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107c01 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c01 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x107c01 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x107c01 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x107c06 [0x48, 0x33, 0x94, 0xEC, 0xC0, 0x01, 0x00, 0x00] (LoadPre 0x107c06 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1c0)) s (0x107c06 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107c06 2 (.sib 4 (some 5) 3 (.d32 0x1c0)))
      [.gpr 2, .gpr 4, .gpr 5] [] [.reg 2, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107c06 2 (.sib 4 (some 5) 3 (.d32 0x1c0))).toInstrSpec (xor_r64_m64_effect_step 0x107c06 0x48 (by decide) 2 (.sib 4 (some 5) 3 (.d32 0x1c0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x107c0e [0x48, 0x89, 0x54, 0x24, 0x30] (StorePre 0x107c0e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107c0e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107c0e 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107c0e 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x107c0e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x107c13 [0x48, 0x8B, 0x4C, 0x24, 0x38] (LoadPre 0x107c13 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107c13 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c13 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x107c13 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x107c13 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x107c18 [0x48, 0x33, 0x8C, 0xEC, 0xC8, 0x01, 0x00, 0x00] (LoadPre 0x107c18 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1c8)) s (0x107c18 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107c18 1 (.sib 4 (some 5) 3 (.d32 0x1c8)))
      [.gpr 1, .gpr 4, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107c18 1 (.sib 4 (some 5) 3 (.d32 0x1c8))).toInstrSpec (xor_r64_m64_effect_step 0x107c18 0x48 (by decide) 1 (.sib 4 (some 5) 3 (.d32 0x1c8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bac) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 55), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bb1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 55), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bb9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 55), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bbe) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bc6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bcb) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 63), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bd0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bd8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bdd) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 68), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107be2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bea) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bef) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 73), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bf4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bfc) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c01) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(2, 78), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c06) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c0e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c13) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(1, 83), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c18) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c20) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107ba7_1 code

theorem block_l107ba7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107ba7 :=
  Rest.liftedBlock (rest_l107ba7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107ba7 x hx)

theorem rest_l107c41 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107c41 bytes_l107c41) (entryMap (live .l107c41))
      3 0x107c41 bytes_l107c41 b_l107c41 := by
  have f0 : InstrSpec 0x107c41 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107c41) (movR32Imm32Effect 0x107c41 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x107c41 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x107c41 0xbe (by decide) 0x8) pre_rip
  have f1 : InstrSpec 0x107c46 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x107c46) (leaR64Effect 0x107c46 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x107c46 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x107c46 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x107c4b [0xE8, 0x40, 0x92, 0xFF, 0xFF] (PushPre 0x107c4b 5) (callEffect (fun _ => 0x100e90) 0x107c50)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107c4b 0x100e90 0x107c50).toInstrSpec (call_rel32_effect_step 0x107c4b 0xffff9240 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c46) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c4b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 53), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e90) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l107c41 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107c41 :=
  Rest.liftedBlock (rest_l107c41 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107c41 x hx)

theorem rest_l107c50_6 [Bindings] (code : CodeMap) :
    Rest (n := 283) code lifted (codeRange 0x107c50 bytes_l107c50) [(0, 276), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]
      17 0x107e48 bytes_l107c50_6 b_l107c50_6 := by
  have f120 : InstrSpec 0x107e48 [0x48, 0x8B, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x107e48 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107e48 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107e48 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x107e48 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x107e48 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f121 : InstrSpec 0x107e50 [0x4C, 0x31, 0xEA] (fun s => s.RIP = 0x107e50) (xorR64R64Effect 0x107e50 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107e50 2 13).toInstrSpec (xor_r64_r64_effect_step 0x107e50 0x4c 0xea (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x107e53 [0x4C, 0x31, 0xEE] (fun s => s.RIP = 0x107e53) (xorR64R64Effect 0x107e53 6 13)
      [.gpr 6, .gpr 13] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107e53 6 13).toInstrSpec (xor_r64_r64_effect_step 0x107e53 0x4c 0xee (by decide) (by decide)) pre_rip
  have f123 : InstrSpec 0x107e56 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x107e56) (movR64R64Effect 0x107e56 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x107e56 0 2).toInstrSpec (mov_r64_r64_effect_step 0x107e56 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f124 : InstrSpec 0x107e59 [0x48, 0xC1, 0xC0, 0x20] (fun s => s.RIP = 0x107e59) (rolR64Effect 0x107e59 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x107e59 4 0 32).toInstrSpec (rol_r64_imm8_effect_step 0x107e59 0x48 0xc0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f125 : InstrSpec 0x107e5d [0x48, 0x33, 0x84, 0xEC, 0x08, 0x02, 0x00, 0x00] (LoadPre 0x107e5d (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x208)) s (0x107e5d + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107e5d 0 (.sib 4 (some 5) 3 (.d32 0x208)))
      [.gpr 0, .gpr 4, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107e5d 0 (.sib 4 (some 5) 3 (.d32 0x208))).toInstrSpec (xor_r64_m64_effect_step 0x107e5d 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x208)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f126 : InstrSpec 0x107e65 [0x48, 0x31, 0xC6] (fun s => s.RIP = 0x107e65) (xorR64R64Effect 0x107e65 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107e65 6 0).toInstrSpec (xor_r64_r64_effect_step 0x107e65 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f127 : InstrSpec 0x107e68 [0x48, 0x89, 0x74, 0x24, 0x38] (StorePre 0x107e68 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107e68 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107e68 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107e68 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x107e68 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f128 : InstrSpec 0x107e6d [0x48, 0x31, 0xCA] (fun s => s.RIP = 0x107e6d) (xorR64R64Effect 0x107e6d 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107e6d 2 1).toInstrSpec (xor_r64_r64_effect_step 0x107e6d 0x48 0xca (by decide) (by decide)) pre_rip
  have f129 : InstrSpec 0x107e70 [0x49, 0xC1, 0xC6, 0x20] (fun s => s.RIP = 0x107e70) (rolR64Effect 0x107e70 4 14 32)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (rolR64Effect_footprint 0x107e70 4 14 32).toInstrSpec (rol_r64_imm8_effect_step 0x107e70 0x49 0xc6 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f130 : InstrSpec 0x107e74 [0x4C, 0x33, 0xB4, 0xEC, 0x10, 0x02, 0x00, 0x00] (LoadPre 0x107e74 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x210)) s (0x107e74 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107e74 14 (.sib 4 (some 5) 3 (.d32 0x210)))
      [.gpr 14, .gpr 4, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107e74 14 (.sib 4 (some 5) 3 (.d32 0x210))).toInstrSpec (xor_r64_m64_effect_step 0x107e74 0x4c (by decide) 6 (.sib 4 (some 5) 3 (.d32 0x210)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f131 : InstrSpec 0x107e7c [0x4C, 0x31, 0xF2] (fun s => s.RIP = 0x107e7c) (xorR64R64Effect 0x107e7c 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107e7c 2 14).toInstrSpec (xor_r64_r64_effect_step 0x107e7c 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f132 : InstrSpec 0x107e7f [0x48, 0x89, 0x54, 0x24, 0x40] (StorePre 0x107e7f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107e7f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107e7f 2 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107e7f 2 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x107e7f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f133 : InstrSpec 0x107e84 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107e84) (movR32Imm32Effect 0x107e84 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x107e84 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x107e84 0xbe (by decide) 0x8) pre_rip
  have f134 : InstrSpec 0x107e89 [0x48, 0x8D, 0x5C, 0x24, 0x08] (fun s => s.RIP = 0x107e89) (leaR64Effect 0x107e89 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x107e89 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x107e89 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f135 : InstrSpec 0x107e8e [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x107e8e) (movR64R64Effect 0x107e8e 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x107e8e 7 3).toInstrSpec (mov_r64_r64_effect_step 0x107e8e 0x48 0xdf (by decide) (by decide)) pre_rip
  have f136 : InstrSpec 0x107e91 [0xE8, 0xFA, 0x8F, 0xFF, 0xFF] (PushPre 0x107e91 5) (callEffect (fun _ => 0x100e90) 0x107e96)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107e91 0x100e90 0x107e96).toInstrSpec (call_rel32_effect_step 0x107e91 0xffff8ffa (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 283) (RestInside.out (n := 283) f120 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 284) (ρ' := [(0, 276), (1, 187), (2, 283), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e50) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 285) (RestInside.out (n := 285) f121 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 286) (ρ' := [(0, 276), (1, 187), (2, 285), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e53) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 287) (RestInside.out (n := 287) f122 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 288) (ρ' := [(0, 276), (1, 187), (2, 285), (3, 216), (4, 4), (5, 5), (6, 287), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e56) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 289) (RestInside.out (n := 289) f123 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 290) (ρ' := [(0, 289), (1, 187), (2, 285), (3, 216), (4, 4), (5, 5), (6, 287), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e59) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 291) (RestInside.out (n := 291) f124 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 292) (ρ' := [(0, 291), (1, 187), (2, 285), (3, 216), (4, 4), (5, 5), (6, 287), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e5d) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 293) (RestInside.out (n := 293) f125 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 294) (ρ' := [(0, 293), (1, 187), (2, 285), (3, 216), (4, 4), (5, 5), (6, 287), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e65) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 295) (RestInside.out (n := 295) f126 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 296) (ρ' := [(0, 293), (1, 187), (2, 285), (3, 216), (4, 4), (5, 5), (6, 295), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e68) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 297) (RestInside.exec (n := 297) (ρ' := [(0, 293), (1, 187), (2, 285), (3, 216), (4, 4), (5, 5), (6, 295), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e6d) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 298) (RestInside.out (n := 298) f128 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 299) (ρ' := [(0, 293), (1, 187), (2, 298), (3, 216), (4, 4), (5, 5), (6, 295), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e70) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 300) (RestInside.out (n := 300) f129 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 301) (ρ' := [(0, 293), (1, 187), (2, 298), (3, 216), (4, 4), (5, 5), (6, 295), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 300), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e74) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f130 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 303) (ρ' := [(0, 293), (1, 187), (2, 298), (3, 216), (4, 4), (5, 5), (6, 295), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 302), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e7c) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f131 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 305) (ρ' := [(0, 293), (1, 187), (2, 304), (3, 216), (4, 4), (5, 5), (6, 295), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 302), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e7f) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 306) (RestInside.exec (n := 306) (ρ' := [(0, 293), (1, 187), (2, 304), (3, 216), (4, 4), (5, 5), (6, 295), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 302), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e84) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 307) (RestInside.out (n := 307) f133 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 308) (ρ' := [(0, 293), (1, 187), (2, 304), (3, 216), (4, 4), (5, 5), (6, 307), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 302), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e89) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 309) (RestInside.out (n := 309) f134 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 310) (ρ' := [(0, 293), (1, 187), (2, 304), (3, 309), (4, 4), (5, 5), (6, 307), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 302), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e8e) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 311) (RestInside.out (n := 311) f135 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 312) (ρ' := [(0, 293), (1, 187), (2, 304), (3, 309), (4, 4), (5, 5), (6, 307), (7, 311), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 302), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e91) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 313) (RestInside.out (n := 313) f136 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 314) (ρ' := [(0, 293), (1, 187), (2, 304), (3, 309), (4, 313), (5, 5), (6, 307), (7, 311), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 302), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e90) f136 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 315) (by decide) (by decide) rfl rfl

theorem rest_l107c50_5 [Bindings] (code : CodeMap) :
    Rest (n := 246) code lifted (codeRange 0x107c50 bytes_l107c50) [(0, 238), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 244), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]
      37 0x107dee bytes_l107c50_5 b_l107c50_5 := by
  have f100 : InstrSpec 0x107dee [0x4C, 0x8B, 0x44, 0x24, 0x78] (LoadPre 0x107dee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107dee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107dee 8 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x107dee 8 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x107dee 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f101 : InstrSpec 0x107df3 [0x49, 0x31, 0xD0] (fun s => s.RIP = 0x107df3) (xorR64R64Effect 0x107df3 8 2)
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107df3 8 2).toInstrSpec (xor_r64_r64_effect_step 0x107df3 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x107df6 [0x48, 0x89, 0x7C, 0x24, 0x20] (StorePre 0x107df6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107df6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107df6 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107df6 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x107df6 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f103 : InstrSpec 0x107dfb [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x107dfb) (movR64R64Effect 0x107dfb 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x107dfb 0 8).toInstrSpec (mov_r64_r64_effect_step 0x107dfb 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f104 : InstrSpec 0x107dfe [0x48, 0xC1, 0xC0, 0x20] (fun s => s.RIP = 0x107dfe) (rolR64Effect 0x107dfe 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x107dfe 4 0 32).toInstrSpec (rol_r64_imm8_effect_step 0x107dfe 0x48 0xc0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x107e02 [0x48, 0x31, 0xD6] (fun s => s.RIP = 0x107e02) (xorR64R64Effect 0x107e02 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107e02 6 2).toInstrSpec (xor_r64_r64_effect_step 0x107e02 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f106 : InstrSpec 0x107e05 [0x48, 0x33, 0x84, 0xEC, 0xF8, 0x01, 0x00, 0x00] (LoadPre 0x107e05 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1f8)) s (0x107e05 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107e05 0 (.sib 4 (some 5) 3 (.d32 0x1f8)))
      [.gpr 0, .gpr 4, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107e05 0 (.sib 4 (some 5) 3 (.d32 0x1f8))).toInstrSpec (xor_r64_m64_effect_step 0x107e05 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x1f8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f107 : InstrSpec 0x107e0d [0x4C, 0x31, 0xF6] (fun s => s.RIP = 0x107e0d) (xorR64R64Effect 0x107e0d 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107e0d 6 14).toInstrSpec (xor_r64_r64_effect_step 0x107e0d 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x107e10 [0x48, 0x31, 0xC6] (fun s => s.RIP = 0x107e10) (xorR64R64Effect 0x107e10 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107e10 6 0).toInstrSpec (xor_r64_r64_effect_step 0x107e10 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f109 : InstrSpec 0x107e13 [0x48, 0x8B, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x107e13 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x107e13 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107e13 2 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x107e13 2 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x107e13 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f110 : InstrSpec 0x107e1b [0x48, 0x8B, 0xBC, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x107e1b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107e1b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107e1b 7 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x107e1b 7 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x107e1b 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f111 : InstrSpec 0x107e23 [0x48, 0x31, 0xFA] (fun s => s.RIP = 0x107e23) (xorR64R64Effect 0x107e23 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107e23 2 7).toInstrSpec (xor_r64_r64_effect_step 0x107e23 0x48 0xfa (by decide) (by decide)) pre_rip
  have f112 : InstrSpec 0x107e26 [0x48, 0x89, 0x74, 0x24, 0x28] (StorePre 0x107e26 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107e26 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107e26 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107e26 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x107e26 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f113 : InstrSpec 0x107e2b [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x107e2b) (movR64R64Effect 0x107e2b 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x107e2b 0 2).toInstrSpec (mov_r64_r64_effect_step 0x107e2b 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f114 : InstrSpec 0x107e2e [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x107e2e) (movR64R64Effect 0x107e2e 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x107e2e 6 2).toInstrSpec (mov_r64_r64_effect_step 0x107e2e 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x107e31 [0x48, 0xC1, 0xC0, 0x20] (fun s => s.RIP = 0x107e31) (rolR64Effect 0x107e31 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x107e31 4 0 32).toInstrSpec (rol_r64_imm8_effect_step 0x107e31 0x48 0xc0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f116 : InstrSpec 0x107e35 [0x48, 0x33, 0x84, 0xEC, 0x00, 0x02, 0x00, 0x00] (LoadPre 0x107e35 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x200)) s (0x107e35 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107e35 0 (.sib 4 (some 5) 3 (.d32 0x200)))
      [.gpr 0, .gpr 4, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107e35 0 (.sib 4 (some 5) 3 (.d32 0x200))).toInstrSpec (xor_r64_m64_effect_step 0x107e35 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x200)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f117 : InstrSpec 0x107e3d [0x49, 0x31, 0xF8] (fun s => s.RIP = 0x107e3d) (xorR64R64Effect 0x107e3d 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107e3d 8 7).toInstrSpec (xor_r64_r64_effect_step 0x107e3d 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x107e40 [0x49, 0x31, 0xC0] (fun s => s.RIP = 0x107e40) (xorR64R64Effect 0x107e40 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107e40 8 0).toInstrSpec (xor_r64_r64_effect_step 0x107e40 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f119 : InstrSpec 0x107e43 [0x4C, 0x89, 0x44, 0x24, 0x30] (StorePre 0x107e43 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107e43 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107e43 8 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107e43 8 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x107e43 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 246) (RestInside.out (n := 246) f100 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 247) (ρ' := [(0, 238), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 244), (8, 246), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107df3) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 248) (RestInside.out (n := 248) f101 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 249) (ρ' := [(0, 238), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107df6) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 250) (RestInside.exec (n := 250) (ρ' := [(0, 238), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dfb) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 251) (RestInside.out (n := 251) f103 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 252) (ρ' := [(0, 251), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dfe) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 253) (RestInside.out (n := 253) f104 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 254) (ρ' := [(0, 253), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e02) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 255) (RestInside.out (n := 255) f105 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 256) (ρ' := [(0, 253), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 255), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e05) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 257) (RestInside.out (n := 257) f106 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 258) (ρ' := [(0, 257), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 255), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e0d) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f107 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 260) (ρ' := [(0, 257), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 259), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e10) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 261) (RestInside.out (n := 261) f108 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 262) (ρ' := [(0, 257), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 261), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e13) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 263) (RestInside.out (n := 263) f109 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 264) (ρ' := [(0, 257), (1, 187), (2, 263), (3, 216), (4, 4), (5, 5), (6, 261), (7, 244), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e1b) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 265) (RestInside.out (n := 265) f110 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 266) (ρ' := [(0, 257), (1, 187), (2, 263), (3, 216), (4, 4), (5, 5), (6, 261), (7, 265), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e23) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 267) (RestInside.out (n := 267) f111 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 268) (ρ' := [(0, 257), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 261), (7, 265), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e26) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 269) (RestInside.exec (n := 269) (ρ' := [(0, 257), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 261), (7, 265), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e2b) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 270) (RestInside.out (n := 270) f113 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 271) (ρ' := [(0, 270), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 261), (7, 265), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e2e) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 272) (RestInside.out (n := 272) f114 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 273) (ρ' := [(0, 270), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e31) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 274) (RestInside.out (n := 274) f115 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 275) (ρ' := [(0, 274), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e35) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 276) (RestInside.out (n := 276) f116 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 277) (ρ' := [(0, 276), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 248), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e3d) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 278) (RestInside.out (n := 278) f117 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 279) (ρ' := [(0, 276), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 278), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e40) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 280) (RestInside.out (n := 280) f118 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 281) (ρ' := [(0, 276), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e43) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 282) (RestInside.exec (n := 282) (ρ' := [(0, 276), (1, 187), (2, 267), (3, 216), (4, 4), (5, 5), (6, 272), (7, 265), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e48) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107c50_6 code

theorem rest_l107c50_4 [Bindings] (code : CodeMap) :
    Rest (n := 208) code lifted (codeRange 0x107c50 bytes_l107c50) [(0, 111), (1, 187), (2, 138), (3, 206), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]
      57 0x107d9c bytes_l107c50_4 b_l107c50_4 := by
  have f80 : InstrSpec 0x107d9c [0x4D, 0x89, 0xD8] (fun s => s.RIP = 0x107d9c) (movR64R64Effect 0x107d9c 8 11)
      [.gpr 11] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x107d9c 8 11).toInstrSpec (mov_r64_r64_effect_step 0x107d9c 0x4d 0xd8 (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x107d9f [0x49, 0xC1, 0xC0, 0x20] (fun s => s.RIP = 0x107d9f) (rolR64Effect 0x107d9f 4 8 32)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (rolR64Effect_footprint 0x107d9f 4 8 32).toInstrSpec (rol_r64_imm8_effect_step 0x107d9f 0x49 0xc0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x107da3 [0x4C, 0x33, 0x84, 0xEC, 0xE0, 0x01, 0x00, 0x00] (LoadPre 0x107da3 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1e0)) s (0x107da3 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107da3 8 (.sib 4 (some 5) 3 (.d32 0x1e0)))
      [.gpr 8, .gpr 4, .gpr 5] [] [.reg 8, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107da3 8 (.sib 4 (some 5) 3 (.d32 0x1e0))).toInstrSpec (xor_r64_m64_effect_step 0x107da3 0x4c (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x1e0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f83 : InstrSpec 0x107dab [0x4C, 0x31, 0xF3] (fun s => s.RIP = 0x107dab) (xorR64R64Effect 0x107dab 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107dab 3 14).toInstrSpec (xor_r64_r64_effect_step 0x107dab 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x107dae [0x4C, 0x31, 0xC3] (fun s => s.RIP = 0x107dae) (xorR64R64Effect 0x107dae 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107dae 3 8).toInstrSpec (xor_r64_r64_effect_step 0x107dae 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x107db1 [0x48, 0x89, 0x5C, 0x24, 0x10] (StorePre 0x107db1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107db1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107db1 3 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107db1 3 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x107db1 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f86 : InstrSpec 0x107db6 [0x48, 0x31, 0xC7] (fun s => s.RIP = 0x107db6) (xorR64R64Effect 0x107db6 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107db6 7 0).toInstrSpec (xor_r64_r64_effect_step 0x107db6 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x107db9 [0x49, 0x31, 0xC3] (fun s => s.RIP = 0x107db9) (xorR64R64Effect 0x107db9 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107db9 11 0).toInstrSpec (xor_r64_r64_effect_step 0x107db9 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x107dbc [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x107dbc) (movR64R64Effect 0x107dbc 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x107dbc 0 7).toInstrSpec (mov_r64_r64_effect_step 0x107dbc 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x107dbf [0x48, 0xC1, 0xC0, 0x20] (fun s => s.RIP = 0x107dbf) (rolR64Effect 0x107dbf 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x107dbf 4 0 32).toInstrSpec (rol_r64_imm8_effect_step 0x107dbf 0x48 0xc0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f90 : InstrSpec 0x107dc3 [0x48, 0x33, 0x84, 0xEC, 0xE8, 0x01, 0x00, 0x00] (LoadPre 0x107dc3 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1e8)) s (0x107dc3 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107dc3 0 (.sib 4 (some 5) 3 (.d32 0x1e8)))
      [.gpr 0, .gpr 4, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107dc3 0 (.sib 4 (some 5) 3 (.d32 0x1e8))).toInstrSpec (xor_r64_m64_effect_step 0x107dc3 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x1e8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f91 : InstrSpec 0x107dcb [0x49, 0x31, 0xC3] (fun s => s.RIP = 0x107dcb) (xorR64R64Effect 0x107dcb 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107dcb 11 0).toInstrSpec (xor_r64_r64_effect_step 0x107dcb 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x107dce [0x4C, 0x31, 0xFE] (fun s => s.RIP = 0x107dce) (xorR64R64Effect 0x107dce 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107dce 6 15).toInstrSpec (xor_r64_r64_effect_step 0x107dce 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f93 : InstrSpec 0x107dd1 [0x4C, 0x89, 0x5C, 0x24, 0x18] (StorePre 0x107dd1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107dd1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107dd1 11 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107dd1 11 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x107dd1 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f94 : InstrSpec 0x107dd6 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x107dd6) (movR64R64Effect 0x107dd6 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x107dd6 0 6).toInstrSpec (mov_r64_r64_effect_step 0x107dd6 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x107dd9 [0x48, 0xC1, 0xC0, 0x20] (fun s => s.RIP = 0x107dd9) (rolR64Effect 0x107dd9 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x107dd9 4 0 32).toInstrSpec (rol_r64_imm8_effect_step 0x107dd9 0x48 0xc0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f96 : InstrSpec 0x107ddd [0x48, 0x33, 0x84, 0xEC, 0xF0, 0x01, 0x00, 0x00] (LoadPre 0x107ddd (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1f0)) s (0x107ddd + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107ddd 0 (.sib 4 (some 5) 3 (.d32 0x1f0)))
      [.gpr 0, .gpr 4, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107ddd 0 (.sib 4 (some 5) 3 (.d32 0x1f0))).toInstrSpec (xor_r64_m64_effect_step 0x107ddd 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x1f0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f97 : InstrSpec 0x107de5 [0x4C, 0x31, 0xFF] (fun s => s.RIP = 0x107de5) (xorR64R64Effect 0x107de5 7 15)
      [.gpr 7, .gpr 15] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107de5 7 15).toInstrSpec (xor_r64_r64_effect_step 0x107de5 0x4c 0xff (by decide) (by decide)) pre_rip
  have f98 : InstrSpec 0x107de8 [0x4C, 0x31, 0xF7] (fun s => s.RIP = 0x107de8) (xorR64R64Effect 0x107de8 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107de8 7 14).toInstrSpec (xor_r64_r64_effect_step 0x107de8 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x107deb [0x48, 0x31, 0xC7] (fun s => s.RIP = 0x107deb) (xorR64R64Effect 0x107deb 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107deb 7 0).toInstrSpec (xor_r64_r64_effect_step 0x107deb 0x48 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f80 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 206), (4, 4), (5, 5), (6, 59), (7, 57), (8, 208), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d9f) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f81 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 206), (4, 4), (5, 5), (6, 59), (7, 57), (8, 210), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107da3) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f82 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 206), (4, 4), (5, 5), (6, 59), (7, 57), (8, 212), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dab) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f83 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 214), (4, 4), (5, 5), (6, 59), (7, 57), (8, 212), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dae) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f84 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 59), (7, 57), (8, 212), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107db1) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 218) (RestInside.exec (n := 218) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 59), (7, 57), (8, 212), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107db6) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f86 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 59), (7, 219), (8, 212), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107db9) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f87 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 59), (7, 219), (8, 212), (9, 201), (10, 197), (11, 221), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dbc) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f88 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(0, 223), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 59), (7, 219), (8, 212), (9, 201), (10, 197), (11, 221), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dbf) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f89 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(0, 225), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 59), (7, 219), (8, 212), (9, 201), (10, 197), (11, 221), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dc3) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f90 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 227), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 59), (7, 219), (8, 212), (9, 201), (10, 197), (11, 221), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dcb) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.out (n := 229) f91 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 230) (ρ' := [(0, 227), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 59), (7, 219), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dce) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.out (n := 231) f92 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 232) (ρ' := [(0, 227), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 219), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dd1) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 233) (RestInside.exec (n := 233) (ρ' := [(0, 227), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 219), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dd6) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f94 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 234), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 219), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dd9) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f95 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 237) (ρ' := [(0, 236), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 219), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ddd) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f96 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 239) (ρ' := [(0, 238), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 219), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107de5) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f97 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 241) (ρ' := [(0, 238), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 240), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107de8) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 242) (RestInside.out (n := 242) f98 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 243) (ρ' := [(0, 238), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 242), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107deb) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 244) (RestInside.out (n := 244) f99 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 245) (ρ' := [(0, 238), (1, 187), (2, 138), (3, 216), (4, 4), (5, 5), (6, 231), (7, 244), (8, 212), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dee) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107c50_5 code

theorem rest_l107c50_3 [Bindings] (code : CodeMap) :
    Rest (n := 169) code lifted (codeRange 0x107c50 bytes_l107c50) [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 161), (11, 55), (12, 156), (13, 167), (14, 163), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]
      77 0x107d46 bytes_l107c50_3 b_l107c50_3 := by
  have f60 : InstrSpec 0x107d46 [0x4C, 0x8B, 0x74, 0x24, 0x40] (LoadPre 0x107d46 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107d46 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107d46 14 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x107d46 14 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x107d46 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f61 : InstrSpec 0x107d4b [0x4D, 0x89, 0xF2] (fun s => s.RIP = 0x107d4b) (movR64R64Effect 0x107d4b 10 14)
      [.gpr 14] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x107d4b 10 14).toInstrSpec (mov_r64_r64_effect_step 0x107d4b 0x4d 0xf2 (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x107d4e [0x49, 0xC1, 0xC2, 0x28] (fun s => s.RIP = 0x107d4e) (rolR64Effect 0x107d4e 4 10 40)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR64Effect_footprint 0x107d4e 4 10 40).toInstrSpec (rol_r64_imm8_effect_step 0x107d4e 0x49 0xc2 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x107d52 [0x48, 0xB9, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00] (fun s => s.RIP = 0x107d52) (movR64Imm64Effect 0x107d52 1 0xff00ff00ff00ff)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x107d52 1 0xff00ff00ff00ff).toInstrSpec (mov_r64_imm64_effect_step 0x107d52 0x48 0xb9 (by decide) (by decide) 0xff00ff00ff00ff) pre_rip
  have f64 : InstrSpec 0x107d5c [0x49, 0x21, 0xCA] (fun s => s.RIP = 0x107d5c) (andR64R64Effect 0x107d5c 10 1)
      [.gpr 10, .gpr 1] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107d5c 10 1).toInstrSpec (and_r64_r64_effect_step 0x107d5c 0x49 0xca (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x107d5f [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x107d5f) (movR64R64Effect 0x107d5f 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x107d5f 1 14).toInstrSpec (mov_r64_r64_effect_step 0x107d5f 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x107d62 [0x48, 0xC1, 0xC1, 0x38] (fun s => s.RIP = 0x107d62) (rolR64Effect 0x107d62 4 1 56)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR64Effect_footprint 0x107d62 4 1 56).toInstrSpec (rol_r64_imm8_effect_step 0x107d62 0x48 0xc1 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x107d66 [0x49, 0xBC, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF] (fun s => s.RIP = 0x107d66) (movR64Imm64Effect 0x107d66 12 0xff00ff00ff00ff00)
      [] [] [.reg 12, .rip] :=
    (movR64Imm64Effect_footprint 0x107d66 12 0xff00ff00ff00ff00).toInstrSpec (mov_r64_imm64_effect_step 0x107d66 0x49 0xbc (by decide) (by decide) 0xff00ff00ff00ff00) pre_rip
  have f68 : InstrSpec 0x107d70 [0x4C, 0x21, 0xE1] (fun s => s.RIP = 0x107d70) (andR64R64Effect 0x107d70 1 12)
      [.gpr 1, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107d70 1 12).toInstrSpec (and_r64_r64_effect_step 0x107d70 0x4c 0xe1 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x107d73 [0x4C, 0x09, 0xD1] (fun s => s.RIP = 0x107d73) (orR64R64Effect 0x107d73 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x107d73 1 10).toInstrSpec (or_r64_r64_effect_step 0x107d73 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x107d76 [0x4C, 0x31, 0xCB] (fun s => s.RIP = 0x107d76) (xorR64R64Effect 0x107d76 3 9)
      [.gpr 3, .gpr 9] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107d76 3 9).toInstrSpec (xor_r64_r64_effect_step 0x107d76 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x107d79 [0x49, 0x31, 0xCE] (fun s => s.RIP = 0x107d79) (xorR64R64Effect 0x107d79 14 1)
      [.gpr 14, .gpr 1] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107d79 14 1).toInstrSpec (xor_r64_r64_effect_step 0x107d79 0x49 0xce (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x107d7c [0x49, 0x89, 0xDA] (fun s => s.RIP = 0x107d7c) (movR64R64Effect 0x107d7c 10 3)
      [.gpr 3] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x107d7c 10 3).toInstrSpec (mov_r64_r64_effect_step 0x107d7c 0x49 0xda (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x107d7f [0x49, 0xC1, 0xC2, 0x20] (fun s => s.RIP = 0x107d7f) (rolR64Effect 0x107d7f 4 10 32)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR64Effect_footprint 0x107d7f 4 10 32).toInstrSpec (rol_r64_imm8_effect_step 0x107d7f 0x49 0xc2 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x107d83 [0x4C, 0x33, 0x94, 0xEC, 0xD8, 0x01, 0x00, 0x00] (LoadPre 0x107d83 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1d8)) s (0x107d83 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107d83 10 (.sib 4 (some 5) 3 (.d32 0x1d8)))
      [.gpr 10, .gpr 4, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107d83 10 (.sib 4 (some 5) 3 (.d32 0x1d8))).toInstrSpec (xor_r64_m64_effect_step 0x107d83 0x4c (by decide) 2 (.sib 4 (some 5) 3 (.d32 0x1d8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f75 : InstrSpec 0x107d8b [0x4D, 0x31, 0xF1] (fun s => s.RIP = 0x107d8b) (xorR64R64Effect 0x107d8b 9 14)
      [.gpr 9, .gpr 14] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107d8b 9 14).toInstrSpec (xor_r64_r64_effect_step 0x107d8b 0x4d 0xf1 (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x107d8e [0x4D, 0x31, 0xD1] (fun s => s.RIP = 0x107d8e) (xorR64R64Effect 0x107d8e 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107d8e 9 10).toInstrSpec (xor_r64_r64_effect_step 0x107d8e 0x4d 0xd1 (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x107d91 [0x4C, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x107d91 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107d91 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107d91 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107d91 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x107d91 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f78 : InstrSpec 0x107d96 [0x4D, 0x31, 0xC3] (fun s => s.RIP = 0x107d96) (xorR64R64Effect 0x107d96 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107d96 11 8).toInstrSpec (xor_r64_r64_effect_step 0x107d96 0x4d 0xc3 (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x107d99 [0x4C, 0x31, 0xC3] (fun s => s.RIP = 0x107d99) (xorR64R64Effect 0x107d99 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107d99 3 8).toInstrSpec (xor_r64_r64_effect_step 0x107d99 0x4c 0xc3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f60 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 161), (11, 55), (12, 156), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d4b) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f61 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 171), (11, 55), (12, 156), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d4e) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f62 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 173), (11, 55), (12, 156), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d52) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f63 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 111), (1, 175), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 173), (11, 55), (12, 156), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d5c) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f64 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 111), (1, 175), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 177), (11, 55), (12, 156), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d5f) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f65 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 111), (1, 179), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 177), (11, 55), (12, 156), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d62) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f66 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 111), (1, 181), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 177), (11, 55), (12, 156), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d66) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f67 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 111), (1, 181), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 177), (11, 55), (12, 183), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d70) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f68 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 111), (1, 185), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 177), (11, 55), (12, 183), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d73) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f69 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 177), (11, 55), (12, 183), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d76) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f70 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 177), (11, 55), (12, 183), (13, 167), (14, 169), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d79) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f71 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 177), (11, 55), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d7c) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f72 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 193), (11, 55), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d7f) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f73 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 195), (11, 55), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d83) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f74 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 197), (11, 55), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d8b) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f75 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 199), (10, 197), (11, 55), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d8e) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f76 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 201), (10, 197), (11, 55), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d91) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.exec (n := 203) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 201), (10, 197), (11, 55), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d96) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f78 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 189), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d99) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f79 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 111), (1, 187), (2, 138), (3, 206), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 201), (10, 197), (11, 204), (12, 183), (13, 167), (14, 191), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d9c) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107c50_4 code

theorem rest_l107c50_2 [Bindings] (code : CodeMap) :
    Rest (n := 132) code lifted (codeRange 0x107c50 bytes_l107c50) [(0, 111), (1, 79), (2, 127), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 130), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]
      97 0x107cef bytes_l107c50_2 b_l107c50_2 := by
  have f40 : InstrSpec 0x107cef [0x4D, 0x21, 0xEA] (fun s => s.RIP = 0x107cef) (andR64R64Effect 0x107cef 10 13)
      [.gpr 10, .gpr 13] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107cef 10 13).toInstrSpec (and_r64_r64_effect_step 0x107cef 0x4d 0xea (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x107cf2 [0x48, 0xC1, 0xC2, 0x38] (fun s => s.RIP = 0x107cf2) (rolR64Effect 0x107cf2 4 2 56)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR64Effect_footprint 0x107cf2 4 2 56).toInstrSpec (rol_r64_imm8_effect_step 0x107cf2 0x48 0xc2 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x107cf6 [0x48, 0x21, 0xCA] (fun s => s.RIP = 0x107cf6) (andR64R64Effect 0x107cf6 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107cf6 2 1).toInstrSpec (and_r64_r64_effect_step 0x107cf6 0x48 0xca (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x107cf9 [0x4C, 0x09, 0xD2] (fun s => s.RIP = 0x107cf9) (orR64R64Effect 0x107cf9 2 10)
      [.gpr 2, .gpr 10] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x107cf9 2 10).toInstrSpec (or_r64_r64_effect_step 0x107cf9 0x4c 0xd2 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x107cfc [0x4C, 0x89, 0xA4, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x107cfc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x107cfc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107cfc 12 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107cfc 12 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x107cfc 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x107d04 [0x4D, 0x89, 0xE2] (fun s => s.RIP = 0x107d04) (movR64R64Effect 0x107d04 10 12)
      [.gpr 12] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x107d04 10 12).toInstrSpec (mov_r64_r64_effect_step 0x107d04 0x4d 0xe2 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x107d07 [0x49, 0xC1, 0xC2, 0x28] (fun s => s.RIP = 0x107d07) (rolR64Effect 0x107d07 4 10 40)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR64Effect_footprint 0x107d07 4 10 40).toInstrSpec (rol_r64_imm8_effect_step 0x107d07 0x49 0xc2 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x107d0b [0x4D, 0x21, 0xEA] (fun s => s.RIP = 0x107d0b) (andR64R64Effect 0x107d0b 10 13)
      [.gpr 10, .gpr 13] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107d0b 10 13).toInstrSpec (and_r64_r64_effect_step 0x107d0b 0x4d 0xea (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x107d0e [0x49, 0xC1, 0xC4, 0x38] (fun s => s.RIP = 0x107d0e) (rolR64Effect 0x107d0e 4 12 56)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (rolR64Effect_footprint 0x107d0e 4 12 56).toInstrSpec (rol_r64_imm8_effect_step 0x107d0e 0x49 0xc4 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x107d12 [0x49, 0x21, 0xCC] (fun s => s.RIP = 0x107d12) (andR64R64Effect 0x107d12 12 1)
      [.gpr 12, .gpr 1] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107d12 12 1).toInstrSpec (and_r64_r64_effect_step 0x107d12 0x49 0xcc (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x107d15 [0x4D, 0x89, 0xF5] (fun s => s.RIP = 0x107d15) (movR64R64Effect 0x107d15 13 14)
      [.gpr 14] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x107d15 13 14).toInstrSpec (mov_r64_r64_effect_step 0x107d15 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x107d18 [0x4C, 0x89, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x107d18 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107d18 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107d18 14 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107d18 14 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x107d18 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x107d20 [0x49, 0xC1, 0xC6, 0x28] (fun s => s.RIP = 0x107d20) (rolR64Effect 0x107d20 4 14 40)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (rolR64Effect_footprint 0x107d20 4 14 40).toInstrSpec (rol_r64_imm8_effect_step 0x107d20 0x49 0xc6 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x107d24 [0x4D, 0x09, 0xD4] (fun s => s.RIP = 0x107d24) (orR64R64Effect 0x107d24 12 10)
      [.gpr 12, .gpr 10] [] [.reg 12, .flags, .rip] :=
    (orR64R64Effect_footprint 0x107d24 12 10).toInstrSpec (or_r64_r64_effect_step 0x107d24 0x4d 0xd4 (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x107d27 [0x4C, 0x89, 0xA4, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x107d27 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107d27 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107d27 12 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107d27 12 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x107d27 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f55 : InstrSpec 0x107d2f [0x49, 0xC1, 0xC5, 0x38] (fun s => s.RIP = 0x107d2f) (rolR64Effect 0x107d2f 4 13 56)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (rolR64Effect_footprint 0x107d2f 4 13 56).toInstrSpec (rol_r64_imm8_effect_step 0x107d2f 0x49 0xc5 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x107d33 [0x49, 0xBA, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00] (fun s => s.RIP = 0x107d33) (movR64Imm64Effect 0x107d33 10 0xff00ff00ff00ff)
      [] [] [.reg 10, .rip] :=
    (movR64Imm64Effect_footprint 0x107d33 10 0xff00ff00ff00ff).toInstrSpec (mov_r64_imm64_effect_step 0x107d33 0x49 0xba (by decide) (by decide) 0xff00ff00ff00ff) pre_rip
  have f57 : InstrSpec 0x107d3d [0x4D, 0x21, 0xD6] (fun s => s.RIP = 0x107d3d) (andR64R64Effect 0x107d3d 14 10)
      [.gpr 14, .gpr 10] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107d3d 14 10).toInstrSpec (and_r64_r64_effect_step 0x107d3d 0x4d 0xd6 (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x107d40 [0x49, 0x21, 0xCD] (fun s => s.RIP = 0x107d40) (andR64R64Effect 0x107d40 13 1)
      [.gpr 13, .gpr 1] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107d40 13 1).toInstrSpec (and_r64_r64_effect_step 0x107d40 0x49 0xcd (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x107d43 [0x4D, 0x09, 0xF5] (fun s => s.RIP = 0x107d43) (orR64R64Effect 0x107d43 13 14)
      [.gpr 13, .gpr 14] [] [.reg 13, .flags, .rip] :=
    (orR64R64Effect_footprint 0x107d43 13 14).toInstrSpec (or_r64_r64_effect_step 0x107d43 0x4d 0xf5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f40 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 111), (1, 79), (2, 127), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 132), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cf2) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f41 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 111), (1, 79), (2, 134), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 132), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cf6) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f42 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 111), (1, 79), (2, 136), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 132), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cf9) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f43 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 132), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cfc) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.exec (n := 140) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 132), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d04) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f45 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 141), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d07) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f46 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 143), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d0b) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f47 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d0e) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f48 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 147), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d12) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f49 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 149), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d15) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f50 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 149), (13, 151), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d18) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.exec (n := 153) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 149), (13, 151), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d20) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f52 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 149), (13, 151), (14, 154), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d24) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f53 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 156), (13, 151), (14, 154), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d27) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.exec (n := 158) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 156), (13, 151), (14, 154), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d2f) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f55 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 145), (11, 55), (12, 156), (13, 159), (14, 154), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d33) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f56 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 161), (11, 55), (12, 156), (13, 159), (14, 154), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d3d) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f57 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 161), (11, 55), (12, 156), (13, 159), (14, 163), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d40) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f58 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 161), (11, 55), (12, 156), (13, 165), (14, 163), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d43) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f59 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 111), (1, 79), (2, 138), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 161), (11, 55), (12, 156), (13, 167), (14, 163), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d46) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107c50_3 code

theorem rest_l107c50_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x107c50 bytes_l107c50) [(0, 89), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 91), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]
      117 0x107cab bytes_l107c50_1 b_l107c50_1 := by
  have f20 : InstrSpec 0x107cab [0x49, 0xC1, 0xC0, 0x38] (fun s => s.RIP = 0x107cab) (rolR64Effect 0x107cab 4 8 56)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (rolR64Effect_footprint 0x107cab 4 8 56).toInstrSpec (rol_r64_imm8_effect_step 0x107cab 0x49 0xc0 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x107caf [0x49, 0x21, 0xC8] (fun s => s.RIP = 0x107caf) (andR64R64Effect 0x107caf 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107caf 8 1).toInstrSpec (and_r64_r64_effect_step 0x107caf 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x107cb2 [0x48, 0x89, 0xFA] (fun s => s.RIP = 0x107cb2) (movR64R64Effect 0x107cb2 2 7)
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x107cb2 2 7).toInstrSpec (mov_r64_r64_effect_step 0x107cb2 0x48 0xfa (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x107cb5 [0x48, 0xC1, 0xC2, 0x28] (fun s => s.RIP = 0x107cb5) (rolR64Effect 0x107cb5 4 2 40)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR64Effect_footprint 0x107cb5 4 2 40).toInstrSpec (rol_r64_imm8_effect_step 0x107cb5 0x48 0xc2 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x107cb9 [0x49, 0x09, 0xC0] (fun s => s.RIP = 0x107cb9) (orR64R64Effect 0x107cb9 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x107cb9 8 0).toInstrSpec (or_r64_r64_effect_step 0x107cb9 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x107cbc [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x107cbc) (movR64R64Effect 0x107cbc 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x107cbc 0 7).toInstrSpec (mov_r64_r64_effect_step 0x107cbc 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x107cbf [0x48, 0xC1, 0xC0, 0x38] (fun s => s.RIP = 0x107cbf) (rolR64Effect 0x107cbf 4 0 56)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x107cbf 4 0 56).toInstrSpec (rol_r64_imm8_effect_step 0x107cbf 0x48 0xc0 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x107cc3 [0x4C, 0x21, 0xEA] (fun s => s.RIP = 0x107cc3) (andR64R64Effect 0x107cc3 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107cc3 2 13).toInstrSpec (and_r64_r64_effect_step 0x107cc3 0x4c 0xea (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x107cc6 [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x107cc6) (andR64R64Effect 0x107cc6 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107cc6 0 1).toInstrSpec (and_r64_r64_effect_step 0x107cc6 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x107cc9 [0x48, 0x09, 0xD0] (fun s => s.RIP = 0x107cc9) (orR64R64Effect 0x107cc9 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x107cc9 0 2).toInstrSpec (or_r64_r64_effect_step 0x107cc9 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x107ccc [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x107ccc) (movR64R64Effect 0x107ccc 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x107ccc 2 6).toInstrSpec (mov_r64_r64_effect_step 0x107ccc 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x107ccf [0x48, 0xC1, 0xC2, 0x28] (fun s => s.RIP = 0x107ccf) (rolR64Effect 0x107ccf 4 2 40)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR64Effect_footprint 0x107ccf 4 2 40).toInstrSpec (rol_r64_imm8_effect_step 0x107ccf 0x48 0xc2 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x107cd3 [0x4C, 0x21, 0xEA] (fun s => s.RIP = 0x107cd3) (andR64R64Effect 0x107cd3 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107cd3 2 13).toInstrSpec (and_r64_r64_effect_step 0x107cd3 0x4c 0xea (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x107cd6 [0x49, 0x89, 0xF7] (fun s => s.RIP = 0x107cd6) (movR64R64Effect 0x107cd6 15 6)
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x107cd6 15 6).toInstrSpec (mov_r64_r64_effect_step 0x107cd6 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x107cd9 [0x49, 0xC1, 0xC7, 0x38] (fun s => s.RIP = 0x107cd9) (rolR64Effect 0x107cd9 4 15 56)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR64Effect_footprint 0x107cd9 4 15 56).toInstrSpec (rol_r64_imm8_effect_step 0x107cd9 0x49 0xc7 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x107cdd [0x49, 0x21, 0xCF] (fun s => s.RIP = 0x107cdd) (andR64R64Effect 0x107cdd 15 1)
      [.gpr 15, .gpr 1] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107cdd 15 1).toInstrSpec (and_r64_r64_effect_step 0x107cdd 0x49 0xcf (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x107ce0 [0x49, 0x09, 0xD7] (fun s => s.RIP = 0x107ce0) (orR64R64Effect 0x107ce0 15 2)
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x107ce0 15 2).toInstrSpec (or_r64_r64_effect_step 0x107ce0 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x107ce3 [0x4C, 0x89, 0xD2] (fun s => s.RIP = 0x107ce3) (movR64R64Effect 0x107ce3 2 10)
      [.gpr 10] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x107ce3 2 10).toInstrSpec (mov_r64_r64_effect_step 0x107ce3 0x4c 0xd2 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x107ce6 [0x4C, 0x89, 0x54, 0x24, 0x78] (StorePre 0x107ce6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107ce6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107ce6 10 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107ce6 10 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x107ce6 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x107ceb [0x49, 0xC1, 0xC2, 0x28] (fun s => s.RIP = 0x107ceb) (rolR64Effect 0x107ceb 4 10 40)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR64Effect_footprint 0x107ceb 4 10 40).toInstrSpec (rol_r64_imm8_effect_step 0x107ceb 0x49 0xc2 0x28 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 89), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 93), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107caf) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 89), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 95), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cb2) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 89), (1, 79), (2, 97), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 95), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cb5) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 89), (1, 79), (2, 99), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 95), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cb9) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 89), (1, 79), (2, 99), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cbc) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 103), (1, 79), (2, 99), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cbf) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 105), (1, 79), (2, 99), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cc3) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 105), (1, 79), (2, 107), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cc6) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 109), (1, 79), (2, 107), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cc9) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 111), (1, 79), (2, 107), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ccc) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 111), (1, 79), (2, 113), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ccf) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 111), (1, 79), (2, 115), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cd3) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f32 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 111), (1, 79), (2, 117), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cd6) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f33 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 111), (1, 79), (2, 117), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (15, 119), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cd9) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f34 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 111), (1, 79), (2, 117), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (15, 121), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cdd) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f35 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 111), (1, 79), (2, 117), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ce0) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f36 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 111), (1, 79), (2, 117), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ce3) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f37 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 111), (1, 79), (2, 127), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ce6) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.exec (n := 129) (ρ' := [(0, 111), (1, 79), (2, 127), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ceb) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f39 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 111), (1, 79), (2, 127), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 101), (9, 83), (10, 130), (11, 55), (12, 63), (13, 71), (14, 65), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cef) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107c50_2 code

theorem rest_l107c50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107c50 bytes_l107c50) (entryMap (live .l107c50))
      137 0x107c50 bytes_l107c50 b_l107c50 := by
  have f0 : InstrSpec 0x107c50 [0x48, 0x8B, 0x5C, 0x24, 0x08] (LoadPre 0x107c50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107c50 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c50 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x107c50 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x107c50 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107c55 [0x4C, 0x8B, 0x5C, 0x24, 0x10] (LoadPre 0x107c55 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107c55 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c55 11 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x107c55 11 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x107c55 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x107c5a [0x48, 0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x107c5a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107c5a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c5a 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x107c5a 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x107c5a 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x107c5f [0x48, 0x8B, 0x74, 0x24, 0x20] (LoadPre 0x107c5f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107c5f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c5f 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x107c5f 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x107c5f 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x107c64 [0x4C, 0x8B, 0x54, 0x24, 0x28] (LoadPre 0x107c64 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107c64 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c64 10 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x107c64 10 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x107c64 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x107c69 [0x4C, 0x8B, 0x64, 0x24, 0x30] (LoadPre 0x107c69 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107c69 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c69 12 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x107c69 12 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x107c69 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x107c6e [0x4C, 0x8B, 0x74, 0x24, 0x38] (LoadPre 0x107c6e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107c6e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c6e 14 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x107c6e 14 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x107c6e 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x107c73 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x107c73) (movR64R64Effect 0x107c73 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x107c73 0 3).toInstrSpec (mov_r64_r64_effect_step 0x107c73 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x107c76 [0x48, 0xC1, 0xC0, 0x28] (fun s => s.RIP = 0x107c76) (rolR64Effect 0x107c76 4 0 40)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x107c76 4 0 40).toInstrSpec (rol_r64_imm8_effect_step 0x107c76 0x48 0xc0 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x107c7a [0x49, 0xBD, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00] (fun s => s.RIP = 0x107c7a) (movR64Imm64Effect 0x107c7a 13 0xff00ff00ff00ff)
      [] [] [.reg 13, .rip] :=
    (movR64Imm64Effect_footprint 0x107c7a 13 0xff00ff00ff00ff).toInstrSpec (mov_r64_imm64_effect_step 0x107c7a 0x49 0xbd (by decide) (by decide) 0xff00ff00ff00ff) pre_rip
  have f10 : InstrSpec 0x107c84 [0x4C, 0x21, 0xE8] (fun s => s.RIP = 0x107c84) (andR64R64Effect 0x107c84 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107c84 0 13).toInstrSpec (and_r64_r64_effect_step 0x107c84 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x107c87 [0x49, 0x89, 0xD9] (fun s => s.RIP = 0x107c87) (movR64R64Effect 0x107c87 9 3)
      [.gpr 3] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x107c87 9 3).toInstrSpec (mov_r64_r64_effect_step 0x107c87 0x49 0xd9 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x107c8a [0x49, 0xC1, 0xC1, 0x38] (fun s => s.RIP = 0x107c8a) (rolR64Effect 0x107c8a 4 9 56)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (rolR64Effect_footprint 0x107c8a 4 9 56).toInstrSpec (rol_r64_imm8_effect_step 0x107c8a 0x49 0xc1 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x107c8e [0x48, 0xB9, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF] (fun s => s.RIP = 0x107c8e) (movR64Imm64Effect 0x107c8e 1 0xff00ff00ff00ff00)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x107c8e 1 0xff00ff00ff00ff00).toInstrSpec (mov_r64_imm64_effect_step 0x107c8e 0x48 0xb9 (by decide) (by decide) 0xff00ff00ff00ff00) pre_rip
  have f14 : InstrSpec 0x107c98 [0x49, 0x21, 0xC9] (fun s => s.RIP = 0x107c98) (andR64R64Effect 0x107c98 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107c98 9 1).toInstrSpec (and_r64_r64_effect_step 0x107c98 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x107c9b [0x49, 0x09, 0xC1] (fun s => s.RIP = 0x107c9b) (orR64R64Effect 0x107c9b 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x107c9b 9 0).toInstrSpec (or_r64_r64_effect_step 0x107c9b 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x107c9e [0x4C, 0x89, 0xD8] (fun s => s.RIP = 0x107c9e) (movR64R64Effect 0x107c9e 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x107c9e 0 11).toInstrSpec (mov_r64_r64_effect_step 0x107c9e 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x107ca1 [0x48, 0xC1, 0xC0, 0x28] (fun s => s.RIP = 0x107ca1) (rolR64Effect 0x107ca1 4 0 40)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x107ca1 4 0 40).toInstrSpec (rol_r64_imm8_effect_step 0x107ca1 0x48 0xc0 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x107ca5 [0x4C, 0x21, 0xE8] (fun s => s.RIP = 0x107ca5) (andR64R64Effect 0x107ca5 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107ca5 0 13).toInstrSpec (and_r64_r64_effect_step 0x107ca5 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x107ca8 [0x4D, 0x89, 0xD8] (fun s => s.RIP = 0x107ca8) (movR64R64Effect 0x107ca8 8 11)
      [.gpr 11] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x107ca8 8 11).toInstrSpec (mov_r64_r64_effect_step 0x107ca8 0x4d 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c55) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (11, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c5a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 53), (4, 4), (5, 5), (7, 57), (11, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c5f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (11, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c64) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (10, 61), (11, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c69) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (10, 61), (11, 55), (12, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c6e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (10, 61), (11, 55), (12, 63), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c73) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (10, 61), (11, 55), (12, 63), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c76) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (10, 61), (11, 55), (12, 63), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c7a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c84) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c87) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 73), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 75), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c8a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 73), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 77), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c8e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 73), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 77), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c98) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 73), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 81), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c9b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 73), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c9e) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ca1) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ca5) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 89), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ca8) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 89), (1, 79), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 91), (9, 83), (10, 61), (11, 55), (12, 63), (13, 71), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cab) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107c50_1 code

theorem block_l107c50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107c50 :=
  Rest.liftedBlock (rest_l107c50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107c50 x hx)

theorem rest_l107e96 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107e96 bytes_l107e96) (entryMap (live .l107e96))
      2 0x107e96 bytes_l107e96 b_l107e96 := by
  have f0 : InstrSpec 0x107e96 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x107e96) (movR64R64Effect 0x107e96 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x107e96 7 3).toInstrSpec (mov_r64_r64_effect_step 0x107e96 0x48 0xdf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x107e99 [0xE8, 0x92, 0x89, 0xFF, 0xFF] (PushPre 0x107e99 5) (callEffect (fun _ => 0x100830) 0x107e9e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107e99 0x100830 0x107e9e).toInstrSpec (call_rel32_effect_step 0x107e99 0xffff8992 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e99) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100830) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l107e96 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107e96 :=
  Rest.liftedBlock (rest_l107e96 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107e96 x hx)

theorem rest_l107e9e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107e9e bytes_l107e9e) (entryMap (live .l107e9e))
      19 0x107e9e bytes_l107e9e b_l107e9e := by
  have f0 : InstrSpec 0x107e9e [0x48, 0x8B, 0x84, 0xEC, 0x18, 0x02, 0x00, 0x00] (LoadPre 0x107e9e (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x218)) s (0x107e9e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107e9e 0 (.sib 4 (some 5) 3 (.d32 0x218)))
      [.gpr 4, .gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107e9e 0 (.sib 4 (some 5) 3 (.d32 0x218))).toInstrSpec (mov_r64_m64_effect_step 0x107e9e 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x218)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107ea6 [0x48, 0x31, 0x44, 0x24, 0x08] (StorePre 0x107ea6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107ea6 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107ea6 5 64 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x107ea6 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (xor_m64_r64_effect_step 0x107ea6 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x107eab [0x48, 0x8B, 0x84, 0xEC, 0x20, 0x02, 0x00, 0x00] (LoadPre 0x107eab (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x220)) s (0x107eab + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107eab 0 (.sib 4 (some 5) 3 (.d32 0x220)))
      [.gpr 4, .gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107eab 0 (.sib 4 (some 5) 3 (.d32 0x220))).toInstrSpec (mov_r64_m64_effect_step 0x107eab 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x220)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x107eb3 [0x48, 0x31, 0x44, 0x24, 0x10] (StorePre 0x107eb3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107eb3 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107eb3 5 64 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x107eb3 5 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (xor_m64_r64_effect_step 0x107eb3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x107eb8 [0x48, 0x8B, 0x84, 0xEC, 0x28, 0x02, 0x00, 0x00] (LoadPre 0x107eb8 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x228)) s (0x107eb8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107eb8 0 (.sib 4 (some 5) 3 (.d32 0x228)))
      [.gpr 4, .gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107eb8 0 (.sib 4 (some 5) 3 (.d32 0x228))).toInstrSpec (mov_r64_m64_effect_step 0x107eb8 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x228)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x107ec0 [0x48, 0x31, 0x44, 0x24, 0x18] (StorePre 0x107ec0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107ec0 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107ec0 5 64 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x107ec0 5 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (xor_m64_r64_effect_step 0x107ec0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x107ec5 [0x48, 0x8B, 0x84, 0xEC, 0x30, 0x02, 0x00, 0x00] (LoadPre 0x107ec5 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x230)) s (0x107ec5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107ec5 0 (.sib 4 (some 5) 3 (.d32 0x230)))
      [.gpr 4, .gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107ec5 0 (.sib 4 (some 5) 3 (.d32 0x230))).toInstrSpec (mov_r64_m64_effect_step 0x107ec5 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x230)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x107ecd [0x48, 0x31, 0x44, 0x24, 0x20] (StorePre 0x107ecd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107ecd + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107ecd 5 64 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x107ecd 5 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (xor_m64_r64_effect_step 0x107ecd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x107ed2 [0x48, 0x8B, 0x84, 0xEC, 0x38, 0x02, 0x00, 0x00] (LoadPre 0x107ed2 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x238)) s (0x107ed2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107ed2 0 (.sib 4 (some 5) 3 (.d32 0x238)))
      [.gpr 4, .gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107ed2 0 (.sib 4 (some 5) 3 (.d32 0x238))).toInstrSpec (mov_r64_m64_effect_step 0x107ed2 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x238)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x107eda [0x48, 0x31, 0x44, 0x24, 0x28] (StorePre 0x107eda 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107eda + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107eda 5 64 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x107eda 5 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (xor_m64_r64_effect_step 0x107eda 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x107edf [0x48, 0x8B, 0x84, 0xEC, 0x40, 0x02, 0x00, 0x00] (LoadPre 0x107edf (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x240)) s (0x107edf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107edf 0 (.sib 4 (some 5) 3 (.d32 0x240)))
      [.gpr 4, .gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107edf 0 (.sib 4 (some 5) 3 (.d32 0x240))).toInstrSpec (mov_r64_m64_effect_step 0x107edf 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x240)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x107ee7 [0x48, 0x31, 0x44, 0x24, 0x30] (StorePre 0x107ee7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107ee7 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107ee7 5 64 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x107ee7 5 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (xor_m64_r64_effect_step 0x107ee7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x107eec [0x48, 0x8B, 0x84, 0xEC, 0x48, 0x02, 0x00, 0x00] (LoadPre 0x107eec (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x248)) s (0x107eec + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107eec 0 (.sib 4 (some 5) 3 (.d32 0x248)))
      [.gpr 4, .gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107eec 0 (.sib 4 (some 5) 3 (.d32 0x248))).toInstrSpec (mov_r64_m64_effect_step 0x107eec 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x248)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x107ef4 [0x48, 0x31, 0x44, 0x24, 0x38] (StorePre 0x107ef4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107ef4 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107ef4 5 64 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x107ef4 5 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (xor_m64_r64_effect_step 0x107ef4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x107ef9 [0x48, 0x8B, 0x84, 0xEC, 0x50, 0x02, 0x00, 0x00] (LoadPre 0x107ef9 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x250)) s (0x107ef9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107ef9 0 (.sib 4 (some 5) 3 (.d32 0x250)))
      [.gpr 4, .gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107ef9 0 (.sib 4 (some 5) 3 (.d32 0x250))).toInstrSpec (mov_r64_m64_effect_step 0x107ef9 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x250)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x107f01 [0x48, 0x31, 0x44, 0x24, 0x40] (StorePre 0x107f01 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107f01 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107f01 5 64 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect64_footprint 0x107f01 5 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (xor_m64_r64_effect_step 0x107f01 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x107f06 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107f06) (movR32Imm32Effect 0x107f06 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x107f06 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x107f06 0xbe (by decide) 0x8) pre_rip
  have f17 : InstrSpec 0x107f0b [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x107f0b) (movR64R64Effect 0x107f0b 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x107f0b 7 3).toInstrSpec (mov_r64_r64_effect_step 0x107f0b 0x48 0xdf (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x107f0e [0xE8, 0x7D, 0x8F, 0xFF, 0xFF] (PushPre 0x107f0e 5) (callEffect (fun _ => 0x100e90) 0x107f13)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107f0e 0x100e90 0x107f13).toInstrSpec (call_rel32_effect_step 0x107f0e 0xffff8f7d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ea6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107eab) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107eb3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107eb8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ec0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ec5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ecd) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ed2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107eda) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107edf) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ee7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107eec) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ef4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ef9) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f01) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f06) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (6, 77), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f0b) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (6, 77), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f0e) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 74), (3, 3), (4, 81), (5, 5), (6, 77), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e90) f18 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 83) (by decide) (by decide) rfl rfl

theorem block_l107e9e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107e9e :=
  Rest.liftedBlock (rest_l107e9e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107e9e x hx)

theorem rest_l107f13_4 [Bindings] (code : CodeMap) :
    Rest (n := 205) code lifted (codeRange 0x107f13 bytes_l107f13) [(0, 198), (1, 193), (2, 89), (3, 202), (4, 4), (5, 5), (6, 191), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x108056 bytes_l107f13_4 b_l107f13_4 := by
  have f80 : InstrSpec 0x108056 [0x48, 0x83, 0xC5, 0x20] (fun s => s.RIP = 0x108056) (addR64Imm8Effect 0x108056 5 0x20)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x108056 5 0x20).toInstrSpec (add_r64_imm8_effect_step 0x108056 0x48 0xc5 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 205) (RestInside.out (n := 205) f80 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 206) (ρ' := [(0, 198), (1, 193), (2, 89), (3, 202), (4, 4), (5, 205), (6, 191), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10805a) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 207) (jmp_rel32_effect_step 0x10805a 0xfffffb21 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l107f13_3 [Bindings] (code : CodeMap) :
    Rest (n := 169) code lifted (codeRange 0x107f13 bytes_l107f13) [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 160), (7, 127), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]
      22 0x107fff bytes_l107f13_3 b_l107f13_3 := by
  have f60 : InstrSpec 0x107fff [0x4C, 0x89, 0x4C, 0x24, 0x20] (StorePre 0x107fff 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107fff + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107fff 9 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107fff 9 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x107fff 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f61 : InstrSpec 0x108004 [0x48, 0x89, 0xCE] (fun s => s.RIP = 0x108004) (movR64R64Effect 0x108004 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x108004 6 1).toInstrSpec (mov_r64_r64_effect_step 0x108004 0x48 0xce (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x108007 [0x48, 0xC1, 0xC6, 0x20] (fun s => s.RIP = 0x108007) (rolR64Effect 0x108007 4 6 32)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR64Effect_footprint 0x108007 4 6 32).toInstrSpec (rol_r64_imm8_effect_step 0x108007 0x48 0xc6 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x10800b [0x48, 0x33, 0xB4, 0xEC, 0x78, 0x02, 0x00, 0x00] (LoadPre 0x10800b (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x278)) s (0x10800b + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x10800b 6 (.sib 4 (some 5) 3 (.d32 0x278)))
      [.gpr 6, .gpr 4, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x10800b 6 (.sib 4 (some 5) 3 (.d32 0x278))).toInstrSpec (xor_r64_m64_effect_step 0x10800b 0x48 (by decide) 6 (.sib 4 (some 5) 3 (.d32 0x278)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f64 : InstrSpec 0x108013 [0x48, 0x31, 0xF7] (fun s => s.RIP = 0x108013) (xorR64R64Effect 0x108013 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108013 7 6).toInstrSpec (xor_r64_r64_effect_step 0x108013 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x108016 [0x48, 0x89, 0x7C, 0x24, 0x28] (StorePre 0x108016 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x108016 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108016 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108016 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x108016 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f66 : InstrSpec 0x10801b [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x10801b) (movR64R64Effect 0x10801b 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10801b 6 3).toInstrSpec (mov_r64_r64_effect_step 0x10801b 0x48 0xde (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x10801e [0x48, 0xC1, 0xC6, 0x30] (fun s => s.RIP = 0x10801e) (rolR64Effect 0x10801e 4 6 48)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR64Effect_footprint 0x10801e 4 6 48).toInstrSpec (rol_r64_imm8_effect_step 0x10801e 0x48 0xc6 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x108022 [0x48, 0x31, 0xF3] (fun s => s.RIP = 0x108022) (xorR64R64Effect 0x108022 3 6)
      [.gpr 3, .gpr 6] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108022 3 6).toInstrSpec (xor_r64_r64_effect_step 0x108022 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x108025 [0x48, 0x31, 0xF1] (fun s => s.RIP = 0x108025) (xorR64R64Effect 0x108025 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108025 1 6).toInstrSpec (xor_r64_r64_effect_step 0x108025 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x108028 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x108028) (movR64R64Effect 0x108028 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x108028 6 3).toInstrSpec (mov_r64_r64_effect_step 0x108028 0x48 0xde (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x10802b [0x48, 0xC1, 0xC6, 0x20] (fun s => s.RIP = 0x10802b) (rolR64Effect 0x10802b 4 6 32)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR64Effect_footprint 0x10802b 4 6 32).toInstrSpec (rol_r64_imm8_effect_step 0x10802b 0x48 0xc6 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x10802f [0x48, 0x33, 0xB4, 0xEC, 0x80, 0x02, 0x00, 0x00] (LoadPre 0x10802f (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x280)) s (0x10802f + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x10802f 6 (.sib 4 (some 5) 3 (.d32 0x280)))
      [.gpr 6, .gpr 4, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x10802f 6 (.sib 4 (some 5) 3 (.d32 0x280))).toInstrSpec (xor_r64_m64_effect_step 0x10802f 0x48 (by decide) 6 (.sib 4 (some 5) 3 (.d32 0x280)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f73 : InstrSpec 0x108037 [0x48, 0x31, 0xF1] (fun s => s.RIP = 0x108037) (xorR64R64Effect 0x108037 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108037 1 6).toInstrSpec (xor_r64_r64_effect_step 0x108037 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x10803a [0x48, 0x89, 0x4C, 0x24, 0x30] (StorePre 0x10803a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10803a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10803a 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10803a 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10803a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f75 : InstrSpec 0x10803f [0x48, 0xC1, 0xC0, 0x20] (fun s => s.RIP = 0x10803f) (rolR64Effect 0x10803f 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x10803f 4 0 32).toInstrSpec (rol_r64_imm8_effect_step 0x10803f 0x48 0xc0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x108043 [0x48, 0x33, 0x84, 0xEC, 0x88, 0x02, 0x00, 0x00] (LoadPre 0x108043 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x288)) s (0x108043 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x108043 0 (.sib 4 (some 5) 3 (.d32 0x288)))
      [.gpr 0, .gpr 4, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x108043 0 (.sib 4 (some 5) 3 (.d32 0x288))).toInstrSpec (xor_r64_m64_effect_step 0x108043 0x48 (by decide) 0 (.sib 4 (some 5) 3 (.d32 0x288)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f77 : InstrSpec 0x10804b [0x48, 0x31, 0xD3] (fun s => s.RIP = 0x10804b) (xorR64R64Effect 0x10804b 3 2)
      [.gpr 3, .gpr 2] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10804b 3 2).toInstrSpec (xor_r64_r64_effect_step 0x10804b 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x10804e [0x48, 0x31, 0xC3] (fun s => s.RIP = 0x10804e) (xorR64R64Effect 0x10804e 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10804e 3 0).toInstrSpec (xor_r64_r64_effect_step 0x10804e 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x108051 [0x48, 0x89, 0x5C, 0x24, 0x38] (StorePre 0x108051 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x108051 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108051 3 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108051 3 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x108051 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 169) (RestInside.exec (n := 169) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 160), (7, 127), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108004) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f61 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 170), (7, 127), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108007) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f62 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 172), (7, 127), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10800b) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f63 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 174), (7, 127), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108013) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.out (n := 176) f64 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 177) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 174), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108016) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.exec (n := 178) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 174), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10801b) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f66 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 179), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10801e) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f67 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 181), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108022) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f68 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 183), (4, 4), (5, 5), (6, 181), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108025) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f69 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 131), (1, 185), (2, 89), (3, 183), (4, 4), (5, 5), (6, 181), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108028) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f70 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 131), (1, 185), (2, 89), (3, 183), (4, 4), (5, 5), (6, 187), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10802b) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f71 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 131), (1, 185), (2, 89), (3, 183), (4, 4), (5, 5), (6, 189), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10802f) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f72 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 131), (1, 185), (2, 89), (3, 183), (4, 4), (5, 5), (6, 191), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108037) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f73 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 131), (1, 193), (2, 89), (3, 183), (4, 4), (5, 5), (6, 191), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10803a) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.exec (n := 195) (ρ' := [(0, 131), (1, 193), (2, 89), (3, 183), (4, 4), (5, 5), (6, 191), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10803f) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 196) (RestInside.out (n := 196) f75 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 197) (ρ' := [(0, 196), (1, 193), (2, 89), (3, 183), (4, 4), (5, 5), (6, 191), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108043) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 198) (RestInside.out (n := 198) f76 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 199) (ρ' := [(0, 198), (1, 193), (2, 89), (3, 183), (4, 4), (5, 5), (6, 191), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10804b) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f77 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 198), (1, 193), (2, 89), (3, 200), (4, 4), (5, 5), (6, 191), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10804e) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f78 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 198), (1, 193), (2, 89), (3, 202), (4, 4), (5, 5), (6, 191), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108051) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 204) (RestInside.exec (n := 204) (ρ' := [(0, 198), (1, 193), (2, 89), (3, 202), (4, 4), (5, 5), (6, 191), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108056) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107f13_4 code

theorem rest_l107f13_2 [Bindings] (code : CodeMap) :
    Rest (n := 133) code lifted (codeRange 0x107f13 bytes_l107f13) [(0, 131), (1, 99), (2, 89), (3, 129), (4, 4), (5, 5), (6, 93), (7, 127), (8, 123), (9, 125), (10, 71), (11, 121), (12, 117), (13, 105), (14, 115), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]
      42 0x107fa2 bytes_l107f13_2 b_l107f13_2 := by
  have f40 : InstrSpec 0x107fa2 [0x49, 0x31, 0xC6] (fun s => s.RIP = 0x107fa2) (xorR64R64Effect 0x107fa2 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107fa2 14 0).toInstrSpec (xor_r64_r64_effect_step 0x107fa2 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x107fa5 [0x4C, 0x33, 0xA4, 0xEC, 0x58, 0x02, 0x00, 0x00] (LoadPre 0x107fa5 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x258)) s (0x107fa5 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107fa5 12 (.sib 4 (some 5) 3 (.d32 0x258)))
      [.gpr 12, .gpr 4, .gpr 5] [] [.reg 12, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107fa5 12 (.sib 4 (some 5) 3 (.d32 0x258))).toInstrSpec (xor_r64_m64_effect_step 0x107fa5 0x4c (by decide) 4 (.sib 4 (some 5) 3 (.d32 0x258)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f42 : InstrSpec 0x107fad [0x49, 0x31, 0xDE] (fun s => s.RIP = 0x107fad) (xorR64R64Effect 0x107fad 14 3)
      [.gpr 14, .gpr 3] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107fad 14 3).toInstrSpec (xor_r64_r64_effect_step 0x107fad 0x49 0xde (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x107fb0 [0x4D, 0x31, 0xE3] (fun s => s.RIP = 0x107fb0) (xorR64R64Effect 0x107fb0 11 12)
      [.gpr 11, .gpr 12] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107fb0 11 12).toInstrSpec (xor_r64_r64_effect_step 0x107fb0 0x4d 0xe3 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x107fb3 [0x48, 0x8B, 0x5C, 0x24, 0x30] (LoadPre 0x107fb3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107fb3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107fb3 3 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x107fb3 3 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x107fb3 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f45 : InstrSpec 0x107fb8 [0x4C, 0x89, 0x74, 0x24, 0x40] (StorePre 0x107fb8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107fb8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107fb8 14 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107fb8 14 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x107fb8 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f46 : InstrSpec 0x107fbd [0x4C, 0x89, 0x5C, 0x24, 0x08] (StorePre 0x107fbd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107fbd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107fbd 11 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107fbd 11 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x107fbd 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f47 : InstrSpec 0x107fc2 [0x49, 0x89, 0xF3] (fun s => s.RIP = 0x107fc2) (movR64R64Effect 0x107fc2 11 6)
      [.gpr 6] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x107fc2 11 6).toInstrSpec (mov_r64_r64_effect_step 0x107fc2 0x49 0xf3 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x107fc5 [0x49, 0xC1, 0xC3, 0x20] (fun s => s.RIP = 0x107fc5) (rolR64Effect 0x107fc5 4 11 32)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (rolR64Effect_footprint 0x107fc5 4 11 32).toInstrSpec (rol_r64_imm8_effect_step 0x107fc5 0x49 0xc3 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x107fc9 [0x4C, 0x33, 0x9C, 0xEC, 0x60, 0x02, 0x00, 0x00] (LoadPre 0x107fc9 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x260)) s (0x107fc9 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107fc9 11 (.sib 4 (some 5) 3 (.d32 0x260)))
      [.gpr 11, .gpr 4, .gpr 5] [] [.reg 11, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107fc9 11 (.sib 4 (some 5) 3 (.d32 0x260))).toInstrSpec (xor_r64_m64_effect_step 0x107fc9 0x4c (by decide) 3 (.sib 4 (some 5) 3 (.d32 0x260)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f50 : InstrSpec 0x107fd1 [0x4D, 0x31, 0xD8] (fun s => s.RIP = 0x107fd1) (xorR64R64Effect 0x107fd1 8 11)
      [.gpr 8, .gpr 11] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107fd1 8 11).toInstrSpec (xor_r64_r64_effect_step 0x107fd1 0x4d 0xd8 (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x107fd4 [0x4C, 0x89, 0x44, 0x24, 0x10] (StorePre 0x107fd4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107fd4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107fd4 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107fd4 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x107fd4 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x107fd9 [0x49, 0xC1, 0xC5, 0x20] (fun s => s.RIP = 0x107fd9) (rolR64Effect 0x107fd9 4 13 32)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (rolR64Effect_footprint 0x107fd9 4 13 32).toInstrSpec (rol_r64_imm8_effect_step 0x107fd9 0x49 0xc5 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x107fdd [0x4C, 0x33, 0xAC, 0xEC, 0x68, 0x02, 0x00, 0x00] (LoadPre 0x107fdd (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x268)) s (0x107fdd + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107fdd 13 (.sib 4 (some 5) 3 (.d32 0x268)))
      [.gpr 13, .gpr 4, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107fdd 13 (.sib 4 (some 5) 3 (.d32 0x268))).toInstrSpec (xor_r64_m64_effect_step 0x107fdd 0x4c (by decide) 5 (.sib 4 (some 5) 3 (.d32 0x268)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f54 : InstrSpec 0x107fe5 [0x4C, 0x31, 0xD6] (fun s => s.RIP = 0x107fe5) (xorR64R64Effect 0x107fe5 6 10)
      [.gpr 6, .gpr 10] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107fe5 6 10).toInstrSpec (xor_r64_r64_effect_step 0x107fe5 0x4c 0xd6 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x107fe8 [0x4C, 0x31, 0xEE] (fun s => s.RIP = 0x107fe8) (xorR64R64Effect 0x107fe8 6 13)
      [.gpr 6, .gpr 13] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107fe8 6 13).toInstrSpec (xor_r64_r64_effect_step 0x107fe8 0x4c 0xee (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x107feb [0x49, 0xC1, 0xC7, 0x20] (fun s => s.RIP = 0x107feb) (rolR64Effect 0x107feb 4 15 32)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR64Effect_footprint 0x107feb 4 15 32).toInstrSpec (rol_r64_imm8_effect_step 0x107feb 0x49 0xc7 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x107fef [0x48, 0x89, 0x74, 0x24, 0x18] (StorePre 0x107fef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107fef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107fef 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107fef 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x107fef 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f58 : InstrSpec 0x107ff4 [0x4C, 0x33, 0xBC, 0xEC, 0x70, 0x02, 0x00, 0x00] (LoadPre 0x107ff4 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x270)) s (0x107ff4 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107ff4 15 (.sib 4 (some 5) 3 (.d32 0x270)))
      [.gpr 15, .gpr 4, .gpr 5] [] [.reg 15, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x107ff4 15 (.sib 4 (some 5) 3 (.d32 0x270))).toInstrSpec (xor_r64_m64_effect_step 0x107ff4 0x4c (by decide) 7 (.sib 4 (some 5) 3 (.d32 0x270)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f59 : InstrSpec 0x107ffc [0x4D, 0x31, 0xF9] (fun s => s.RIP = 0x107ffc) (xorR64R64Effect 0x107ffc 9 15)
      [.gpr 9, .gpr 15] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107ffc 9 15).toInstrSpec (xor_r64_r64_effect_step 0x107ffc 0x4d 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f40 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 129), (4, 4), (5, 5), (6, 93), (7, 127), (8, 123), (9, 125), (10, 71), (11, 121), (12, 117), (13, 105), (14, 133), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fa5) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f41 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 129), (4, 4), (5, 5), (6, 93), (7, 127), (8, 123), (9, 125), (10, 71), (11, 121), (12, 135), (13, 105), (14, 133), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fad) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f42 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 129), (4, 4), (5, 5), (6, 93), (7, 127), (8, 123), (9, 125), (10, 71), (11, 121), (12, 135), (13, 105), (14, 137), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fb0) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f43 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 129), (4, 4), (5, 5), (6, 93), (7, 127), (8, 123), (9, 125), (10, 71), (11, 139), (12, 135), (13, 105), (14, 137), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fb3) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f44 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 93), (7, 127), (8, 123), (9, 125), (10, 71), (11, 139), (12, 135), (13, 105), (14, 137), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fb8) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.exec (n := 143) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 93), (7, 127), (8, 123), (9, 125), (10, 71), (11, 139), (12, 135), (13, 105), (14, 137), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fbd) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 144) (RestInside.exec (n := 144) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 93), (7, 127), (8, 123), (9, 125), (10, 71), (11, 139), (12, 135), (13, 105), (14, 137), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fc2) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f47 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 93), (7, 127), (8, 123), (9, 125), (10, 71), (11, 145), (12, 135), (13, 105), (14, 137), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fc5) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f48 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 93), (7, 127), (8, 123), (9, 125), (10, 71), (11, 147), (12, 135), (13, 105), (14, 137), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fc9) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f49 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 93), (7, 127), (8, 123), (9, 125), (10, 71), (11, 149), (12, 135), (13, 105), (14, 137), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fd1) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f50 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 93), (7, 127), (8, 151), (9, 125), (10, 71), (11, 149), (12, 135), (13, 105), (14, 137), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fd4) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.exec (n := 153) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 93), (7, 127), (8, 151), (9, 125), (10, 71), (11, 149), (12, 135), (13, 105), (14, 137), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fd9) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f52 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 93), (7, 127), (8, 151), (9, 125), (10, 71), (11, 149), (12, 135), (13, 154), (14, 137), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fdd) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f53 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 93), (7, 127), (8, 151), (9, 125), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fe5) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f54 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 158), (7, 127), (8, 151), (9, 125), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fe8) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f55 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 160), (7, 127), (8, 151), (9, 125), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107feb) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f56 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 160), (7, 127), (8, 151), (9, 125), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fef) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.exec (n := 164) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 160), (7, 127), (8, 151), (9, 125), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ff4) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f58 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 160), (7, 127), (8, 151), (9, 125), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ffc) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f59 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 141), (4, 4), (5, 5), (6, 160), (7, 127), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fff) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107f13_3 code

theorem rest_l107f13_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x107f13 bytes_l107f13) [(0, 79), (1, 73), (2, 89), (3, 85), (4, 4), (5, 5), (6, 55), (7, 67), (8, 91), (9, 61), (10, 71), (11, 59), (13, 65), (14, 83), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]
      62 0x107f63 bytes_l107f13_1 b_l107f13_1 := by
  have f20 : InstrSpec 0x107f63 [0x4C, 0x31, 0xEE] (fun s => s.RIP = 0x107f63) (xorR64R64Effect 0x107f63 6 13)
      [.gpr 6, .gpr 13] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107f63 6 13).toInstrSpec (xor_r64_r64_effect_step 0x107f63 0x4c 0xee (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x107f66 [0x4D, 0x31, 0xD1] (fun s => s.RIP = 0x107f66) (xorR64R64Effect 0x107f66 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107f66 9 10).toInstrSpec (xor_r64_r64_effect_step 0x107f66 0x4d 0xd1 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x107f69 [0x4C, 0x31, 0xFF] (fun s => s.RIP = 0x107f69) (xorR64R64Effect 0x107f69 7 15)
      [.gpr 7, .gpr 15] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107f69 7 15).toInstrSpec (xor_r64_r64_effect_step 0x107f69 0x4c 0xff (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x107f6c [0x4C, 0x31, 0xF1] (fun s => s.RIP = 0x107f6c) (xorR64R64Effect 0x107f6c 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107f6c 1 14).toInstrSpec (xor_r64_r64_effect_step 0x107f6c 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x107f6f [0x4D, 0x89, 0xC4] (fun s => s.RIP = 0x107f6f) (movR64R64Effect 0x107f6f 12 8)
      [.gpr 8] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x107f6f 12 8).toInstrSpec (mov_r64_r64_effect_step 0x107f6f 0x4d 0xc4 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x107f72 [0x4D, 0x31, 0xE8] (fun s => s.RIP = 0x107f72) (xorR64R64Effect 0x107f72 8 13)
      [.gpr 8, .gpr 13] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107f72 8 13).toInstrSpec (xor_r64_r64_effect_step 0x107f72 0x4d 0xe8 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x107f75 [0x4D, 0x89, 0xCD] (fun s => s.RIP = 0x107f75) (movR64R64Effect 0x107f75 13 9)
      [.gpr 9] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x107f75 13 9).toInstrSpec (mov_r64_r64_effect_step 0x107f75 0x4d 0xcd (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x107f78 [0x4D, 0x31, 0xF9] (fun s => s.RIP = 0x107f78) (xorR64R64Effect 0x107f78 9 15)
      [.gpr 9, .gpr 15] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107f78 9 15).toInstrSpec (xor_r64_r64_effect_step 0x107f78 0x4d 0xf9 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x107f7b [0x49, 0x89, 0xFF] (fun s => s.RIP = 0x107f7b) (movR64R64Effect 0x107f7b 15 7)
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x107f7b 15 7).toInstrSpec (mov_r64_r64_effect_step 0x107f7b 0x49 0xff (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x107f7e [0x4C, 0x31, 0xF7] (fun s => s.RIP = 0x107f7e) (xorR64R64Effect 0x107f7e 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107f7e 7 14).toInstrSpec (xor_r64_r64_effect_step 0x107f7e 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x107f81 [0x49, 0x89, 0xDE] (fun s => s.RIP = 0x107f81) (movR64R64Effect 0x107f81 14 3)
      [.gpr 3] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x107f81 14 3).toInstrSpec (mov_r64_r64_effect_step 0x107f81 0x49 0xde (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x107f84 [0x49, 0xC1, 0xC6, 0x30] (fun s => s.RIP = 0x107f84) (rolR64Effect 0x107f84 4 14 48)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (rolR64Effect_footprint 0x107f84 4 14 48).toInstrSpec (rol_r64_imm8_effect_step 0x107f84 0x49 0xc6 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x107f88 [0x49, 0xC1, 0xC4, 0x20] (fun s => s.RIP = 0x107f88) (rolR64Effect 0x107f88 4 12 32)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (rolR64Effect_footprint 0x107f88 4 12 32).toInstrSpec (rol_r64_imm8_effect_step 0x107f88 0x49 0xc4 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x107f8c [0x4C, 0x31, 0xF3] (fun s => s.RIP = 0x107f8c) (xorR64R64Effect 0x107f8c 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107f8c 3 14).toInstrSpec (xor_r64_r64_effect_step 0x107f8c 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x107f8f [0x49, 0x31, 0xDB] (fun s => s.RIP = 0x107f8f) (xorR64R64Effect 0x107f8f 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107f8f 11 3).toInstrSpec (xor_r64_r64_effect_step 0x107f8f 0x49 0xdb (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x107f92 [0x49, 0x31, 0xD8] (fun s => s.RIP = 0x107f92) (xorR64R64Effect 0x107f92 8 3)
      [.gpr 8, .gpr 3] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107f92 8 3).toInstrSpec (xor_r64_r64_effect_step 0x107f92 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x107f95 [0x49, 0x31, 0xD9] (fun s => s.RIP = 0x107f95) (xorR64R64Effect 0x107f95 9 3)
      [.gpr 9, .gpr 3] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107f95 9 3).toInstrSpec (xor_r64_r64_effect_step 0x107f95 0x49 0xd9 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x107f98 [0x48, 0x31, 0xDF] (fun s => s.RIP = 0x107f98) (xorR64R64Effect 0x107f98 7 3)
      [.gpr 7, .gpr 3] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107f98 7 3).toInstrSpec (xor_r64_r64_effect_step 0x107f98 0x48 0xdf (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x107f9b [0x48, 0xC1, 0xC3, 0x20] (fun s => s.RIP = 0x107f9b) (rolR64Effect 0x107f9b 4 3 32)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (rolR64Effect_footprint 0x107f9b 4 3 32).toInstrSpec (rol_r64_imm8_effect_step 0x107f9b 0x48 0xc3 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x107f9f [0x48, 0x31, 0xD0] (fun s => s.RIP = 0x107f9f) (xorR64R64Effect 0x107f9f 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107f9f 0 2).toInstrSpec (xor_r64_r64_effect_step 0x107f9f 0x48 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 79), (1, 73), (2, 89), (3, 85), (4, 4), (5, 5), (6, 93), (7, 67), (8, 91), (9, 61), (10, 71), (11, 59), (13, 65), (14, 83), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f66) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 79), (1, 73), (2, 89), (3, 85), (4, 4), (5, 5), (6, 93), (7, 67), (8, 91), (9, 95), (10, 71), (11, 59), (13, 65), (14, 83), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f69) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 79), (1, 73), (2, 89), (3, 85), (4, 4), (5, 5), (6, 93), (7, 97), (8, 91), (9, 95), (10, 71), (11, 59), (13, 65), (14, 83), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f6c) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 79), (1, 99), (2, 89), (3, 85), (4, 4), (5, 5), (6, 93), (7, 97), (8, 91), (9, 95), (10, 71), (11, 59), (13, 65), (14, 83), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f6f) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 79), (1, 99), (2, 89), (3, 85), (4, 4), (5, 5), (6, 93), (7, 97), (8, 91), (9, 95), (10, 71), (11, 59), (12, 101), (13, 65), (14, 83), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f72) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 79), (1, 99), (2, 89), (3, 85), (4, 4), (5, 5), (6, 93), (7, 97), (8, 103), (9, 95), (10, 71), (11, 59), (12, 101), (13, 65), (14, 83), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f75) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 79), (1, 99), (2, 89), (3, 85), (4, 4), (5, 5), (6, 93), (7, 97), (8, 103), (9, 95), (10, 71), (11, 59), (12, 101), (13, 105), (14, 83), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f78) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 79), (1, 99), (2, 89), (3, 85), (4, 4), (5, 5), (6, 93), (7, 97), (8, 103), (9, 107), (10, 71), (11, 59), (12, 101), (13, 105), (14, 83), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f7b) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 79), (1, 99), (2, 89), (3, 85), (4, 4), (5, 5), (6, 93), (7, 97), (8, 103), (9, 107), (10, 71), (11, 59), (12, 101), (13, 105), (14, 83), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f7e) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 79), (1, 99), (2, 89), (3, 85), (4, 4), (5, 5), (6, 93), (7, 111), (8, 103), (9, 107), (10, 71), (11, 59), (12, 101), (13, 105), (14, 83), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f81) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 79), (1, 99), (2, 89), (3, 85), (4, 4), (5, 5), (6, 93), (7, 111), (8, 103), (9, 107), (10, 71), (11, 59), (12, 101), (13, 105), (14, 113), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f84) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 79), (1, 99), (2, 89), (3, 85), (4, 4), (5, 5), (6, 93), (7, 111), (8, 103), (9, 107), (10, 71), (11, 59), (12, 101), (13, 105), (14, 115), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f88) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f32 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 79), (1, 99), (2, 89), (3, 85), (4, 4), (5, 5), (6, 93), (7, 111), (8, 103), (9, 107), (10, 71), (11, 59), (12, 117), (13, 105), (14, 115), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f8c) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f33 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 79), (1, 99), (2, 89), (3, 119), (4, 4), (5, 5), (6, 93), (7, 111), (8, 103), (9, 107), (10, 71), (11, 59), (12, 117), (13, 105), (14, 115), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f8f) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f34 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 79), (1, 99), (2, 89), (3, 119), (4, 4), (5, 5), (6, 93), (7, 111), (8, 103), (9, 107), (10, 71), (11, 121), (12, 117), (13, 105), (14, 115), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f92) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f35 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 79), (1, 99), (2, 89), (3, 119), (4, 4), (5, 5), (6, 93), (7, 111), (8, 123), (9, 107), (10, 71), (11, 121), (12, 117), (13, 105), (14, 115), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f95) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f36 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 79), (1, 99), (2, 89), (3, 119), (4, 4), (5, 5), (6, 93), (7, 111), (8, 123), (9, 125), (10, 71), (11, 121), (12, 117), (13, 105), (14, 115), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f98) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f37 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 79), (1, 99), (2, 89), (3, 119), (4, 4), (5, 5), (6, 93), (7, 127), (8, 123), (9, 125), (10, 71), (11, 121), (12, 117), (13, 105), (14, 115), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f9b) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f38 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 79), (1, 99), (2, 89), (3, 129), (4, 4), (5, 5), (6, 93), (7, 127), (8, 123), (9, 125), (10, 71), (11, 121), (12, 117), (13, 105), (14, 115), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f9f) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f39 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 131), (1, 99), (2, 89), (3, 129), (4, 4), (5, 5), (6, 93), (7, 127), (8, 123), (9, 125), (10, 71), (11, 121), (12, 117), (13, 105), (14, 115), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107fa2) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107f13_2 code

theorem rest_l107f13 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107f13 bytes_l107f13) (entryMap (live .l107f13))
      82 0x107f13 bytes_l107f13 b_l107f13 := by
  have f0 : InstrSpec 0x107f13 [0x4C, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x107f13 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107f13 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f13 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x107f13 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x107f13 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107f18 [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x107f18 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107f18 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f18 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x107f18 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x107f18 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x107f1d [0x4D, 0x89, 0xC3] (fun s => s.RIP = 0x107f1d) (movR64R64Effect 0x107f1d 11 8)
      [.gpr 8] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x107f1d 11 8).toInstrSpec (mov_r64_r64_effect_step 0x107f1d 0x4d 0xc3 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x107f20 [0x49, 0xC1, 0xC3, 0x30] (fun s => s.RIP = 0x107f20) (rolR64Effect 0x107f20 4 11 48)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (rolR64Effect_footprint 0x107f20 4 11 48).toInstrSpec (rol_r64_imm8_effect_step 0x107f20 0x49 0xc3 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x107f24 [0x4C, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x107f24 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107f24 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f24 9 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x107f24 9 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x107f24 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x107f29 [0x49, 0x89, 0xF5] (fun s => s.RIP = 0x107f29) (movR64R64Effect 0x107f29 13 6)
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x107f29 13 6).toInstrSpec (mov_r64_r64_effect_step 0x107f29 0x49 0xf5 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x107f2c [0x49, 0xC1, 0xC5, 0x30] (fun s => s.RIP = 0x107f2c) (rolR64Effect 0x107f2c 4 13 48)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (rolR64Effect_footprint 0x107f2c 4 13 48).toInstrSpec (rol_r64_imm8_effect_step 0x107f2c 0x49 0xc5 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x107f30 [0x48, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x107f30 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107f30 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f30 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x107f30 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x107f30 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x107f35 [0x4D, 0x89, 0xCA] (fun s => s.RIP = 0x107f35) (movR64R64Effect 0x107f35 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x107f35 10 9).toInstrSpec (mov_r64_r64_effect_step 0x107f35 0x4d 0xca (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x107f38 [0x49, 0xC1, 0xC2, 0x30] (fun s => s.RIP = 0x107f38) (rolR64Effect 0x107f38 4 10 48)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR64Effect_footprint 0x107f38 4 10 48).toInstrSpec (rol_r64_imm8_effect_step 0x107f38 0x49 0xc2 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x107f3c [0x48, 0x8B, 0x4C, 0x24, 0x28] (LoadPre 0x107f3c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107f3c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f3c 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x107f3c 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x107f3c 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x107f41 [0x49, 0x89, 0xFF] (fun s => s.RIP = 0x107f41) (movR64R64Effect 0x107f41 15 7)
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x107f41 15 7).toInstrSpec (mov_r64_r64_effect_step 0x107f41 0x49 0xff (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x107f44 [0x49, 0xC1, 0xC7, 0x30] (fun s => s.RIP = 0x107f44) (rolR64Effect 0x107f44 4 15 48)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR64Effect_footprint 0x107f44 4 15 48).toInstrSpec (rol_r64_imm8_effect_step 0x107f44 0x49 0xc7 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x107f48 [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x107f48 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107f48 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f48 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107f48 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x107f48 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x107f4d [0x49, 0x89, 0xCE] (fun s => s.RIP = 0x107f4d) (movR64R64Effect 0x107f4d 14 1)
      [.gpr 1] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x107f4d 14 1).toInstrSpec (mov_r64_r64_effect_step 0x107f4d 0x49 0xce (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x107f50 [0x49, 0xC1, 0xC6, 0x30] (fun s => s.RIP = 0x107f50) (rolR64Effect 0x107f50 4 14 48)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (rolR64Effect_footprint 0x107f50 4 14 48).toInstrSpec (rol_r64_imm8_effect_step 0x107f50 0x49 0xc6 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x107f54 [0x48, 0x8B, 0x5C, 0x24, 0x40] (LoadPre 0x107f54 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107f54 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f54 3 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x107f54 3 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x107f54 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x107f59 [0x48, 0x89, 0xC2] (fun s => s.RIP = 0x107f59) (movR64R64Effect 0x107f59 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x107f59 2 0).toInstrSpec (mov_r64_r64_effect_step 0x107f59 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x107f5c [0x48, 0xC1, 0xC2, 0x30] (fun s => s.RIP = 0x107f5c) (rolR64Effect 0x107f5c 4 2 48)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR64Effect_footprint 0x107f5c 4 2 48).toInstrSpec (rol_r64_imm8_effect_step 0x107f5c 0x48 0xc2 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x107f60 [0x4D, 0x31, 0xD8] (fun s => s.RIP = 0x107f60) (xorR64R64Effect 0x107f60 8 11)
      [.gpr 8, .gpr 11] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x107f60 8 11).toInstrSpec (xor_r64_r64_effect_step 0x107f60 0x4d 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (8, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f18) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (8, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f1d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(4, 4), (5, 5), (6, 55), (8, 53), (11, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f20) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(4, 4), (5, 5), (6, 55), (8, 53), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f24) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(4, 4), (5, 5), (6, 55), (8, 53), (9, 61), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f29) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(4, 4), (5, 5), (6, 55), (8, 53), (9, 61), (11, 59), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f2c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(4, 4), (5, 5), (6, 55), (8, 53), (9, 61), (11, 59), (13, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f30) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 67), (8, 53), (9, 61), (11, 59), (13, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f35) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 67), (8, 53), (9, 61), (10, 69), (11, 59), (13, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f38) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 67), (8, 53), (9, 61), (10, 71), (11, 59), (13, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f3c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 73), (4, 4), (5, 5), (6, 55), (7, 67), (8, 53), (9, 61), (10, 71), (11, 59), (13, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f41) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 73), (4, 4), (5, 5), (6, 55), (7, 67), (8, 53), (9, 61), (10, 71), (11, 59), (13, 65), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f44) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 73), (4, 4), (5, 5), (6, 55), (7, 67), (8, 53), (9, 61), (10, 71), (11, 59), (13, 65), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f48) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 73), (4, 4), (5, 5), (6, 55), (7, 67), (8, 53), (9, 61), (10, 71), (11, 59), (13, 65), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f4d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 79), (1, 73), (4, 4), (5, 5), (6, 55), (7, 67), (8, 53), (9, 61), (10, 71), (11, 59), (13, 65), (14, 81), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f50) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 79), (1, 73), (4, 4), (5, 5), (6, 55), (7, 67), (8, 53), (9, 61), (10, 71), (11, 59), (13, 65), (14, 83), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f54) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 79), (1, 73), (3, 85), (4, 4), (5, 5), (6, 55), (7, 67), (8, 53), (9, 61), (10, 71), (11, 59), (13, 65), (14, 83), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f59) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 79), (1, 73), (2, 87), (3, 85), (4, 4), (5, 5), (6, 55), (7, 67), (8, 53), (9, 61), (10, 71), (11, 59), (13, 65), (14, 83), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f5c) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 79), (1, 73), (2, 89), (3, 85), (4, 4), (5, 5), (6, 55), (7, 67), (8, 53), (9, 61), (10, 71), (11, 59), (13, 65), (14, 83), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f60) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 79), (1, 73), (2, 89), (3, 85), (4, 4), (5, 5), (6, 55), (7, 67), (8, 91), (9, 61), (10, 71), (11, 59), (13, 65), (14, 83), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f63) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l107f13_1 code

theorem block_l107f13 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107f13 :=
  Rest.liftedBlock (rest_l107f13 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107f13 x hx)

theorem rest_l10805f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10805f bytes_l10805f) (entryMap (live .l10805f))
      12 0x10805f bytes_l10805f b_l10805f := by
  have f0 : InstrSpec 0x10805f [0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10805f 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10805f + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10805f (.sib 4 none 0 (.d8 0x40)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10805f (.sib 4 none 0 (.d8 0x40)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10805f 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x108068 [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108068 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x108068 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108068 (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108068 (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108068 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x108071 [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108071 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108071 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108071 (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108071 (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108071 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10807a [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10807a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10807a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10807a (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10807a (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10807a 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x108083 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108083 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x108083 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108083 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108083 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108083 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10808c [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10808c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10808c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10808c (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10808c (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10808c 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x108095 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108095 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108095 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108095 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108095 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108095 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10809e [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10809e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10809e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10809e (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10809e (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10809e 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1080a7 [0x4C, 0x8B, 0xA4, 0x24, 0xE8, 0x00, 0x00, 0x00] (LoadPre 0x1080a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1080a7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1080a7 12 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x1080a7 12 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_r64_m64_effect_step 0x1080a7 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1080af [0x4D, 0x85, 0xE4] (fun s => s.RIP = 0x1080af) (testR64R64Effect 0x1080af 12 12)
      [.gpr 12, .gpr 12] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1080af 12 12).toInstrSpec (test_r64_r64_effect_step 0x1080af 0x4d 0xe4 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1080b2 [0x48, 0x8B, 0xAC, 0x24, 0xF0, 0x00, 0x00, 0x00] (LoadPre 0x1080b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x1080b2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1080b2 5 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x1080b2 5 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x1080b2 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108068) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108071) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10807a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108083) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10808c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108095) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10809e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1080a7) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 61), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1080af) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f9 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 61), (13, 13), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1080b2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 61), (13, 13), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1080ba) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 67) (jcc_rel32_effect_step 0x1080ba 4 0x401) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10805f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10805f :=
  Rest.liftedBlock (rest_l10805f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10805f x hx)

theorem rest_l1080c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1080c0 bytes_l1080c0) (entryMap (live .l1080c0))
      13 0x1080c0 bytes_l1080c0 b_l1080c0 := by
  have f0 : InstrSpec 0x1080c0 [0x48, 0xB8, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F] (fun s => s.RIP = 0x1080c0) (movR64Imm64Effect 0x1080c0 0 0xffffffffffffffc)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x1080c0 0 0xffffffffffffffc).toInstrSpec (mov_r64_imm64_effect_step 0x1080c0 0x48 0xb8 (by decide) (by decide) 0xffffffffffffffc) pre_rip
  have f1 : InstrSpec 0x1080ca [0x48, 0x8B, 0x8C, 0x24, 0x40, 0x01, 0x00, 0x00] (LoadPre 0x1080ca (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1080ca + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1080ca 1 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1080ca 1 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_r64_m64_effect_step 0x1080ca 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1080d2 [0x48, 0x21, 0xC1] (fun s => s.RIP = 0x1080d2) (andR64R64Effect 0x1080d2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1080d2 1 0).toInstrSpec (and_r64_r64_effect_step 0x1080d2 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1080d5 [0x48, 0xC1, 0xE1, 0x04] (fun s => s.RIP = 0x1080d5) (shlR64Effect 0x1080d5 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x1080d5 4 1 4).toInstrSpec (shl_r64_imm8_effect_step 0x1080d5 0x48 0xe1 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1080d9 [0x48, 0x01, 0xCD] (fun s => s.RIP = 0x1080d9) (addR64R64Effect 0x1080d9 5 1)
      [.gpr 5, .gpr 1] [] [.reg 5, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1080d9 5 1).toInstrSpec (add_r64_r64_effect_step 0x1080d9 0x48 0xcd (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1080dc [0x48, 0x01, 0xCA] (fun s => s.RIP = 0x1080dc) (addR64R64Effect 0x1080dc 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1080dc 2 1).toInstrSpec (add_r64_r64_effect_step 0x1080dc 0x48 0xca (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1080df [0x48, 0x89, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x1080df 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1080df + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1080df 2 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1080df 2 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x1080df 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1080e7 [0x41, 0xC1, 0xE4, 0x04] (fun s => s.RIP = 0x1080e7) (shlR32Effect 0x1080e7 4 12 4)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shlR32Effect_footprint 0x1080e7 4 12 4).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1080e7 0x41 0xe4 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1080eb [0x48, 0x8B, 0x9C, 0x24, 0x50, 0x01, 0x00, 0x00] (LoadPre 0x1080eb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x1080eb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1080eb 3 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1080eb 3 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (mov_r64_m64_effect_step 0x1080eb 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1080f3 [0x45, 0x31, 0xED] (fun s => s.RIP = 0x1080f3) (xorR32R32Effect 0x1080f3 3 13 13)
      [.gpr 13, .gpr 13] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1080f3 3 13 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x1080f3 0x45 0xed (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1080f6 [0x4C, 0x8D, 0xB4, 0x24, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1080f6) (leaR64Effect 0x1080f6 14 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x1080f6 14 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (lea_r64_effect_step 0x1080f6 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1080fe [0x4C, 0x8D, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1080fe) (leaR64Effect 0x1080fe 15 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x1080fe 15 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x1080fe 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x108106 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108106) (fun _ => nopEffect 0x108106 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x108106 10).toInstrSpec (nop_m_effect_step 0x108106 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1080ca) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1080d2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (2, 2), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1080d5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 59), (2, 2), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1080d9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 59), (2, 2), (4, 4), (5, 61), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1080dc) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 59), (2, 63), (4, 4), (5, 61), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1080df) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 59), (2, 63), (4, 4), (5, 61), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1080e7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 59), (2, 63), (4, 4), (5, 61), (9, 9), (12, 66), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1080eb) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 59), (2, 63), (3, 68), (4, 4), (5, 61), (9, 9), (12, 66), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1080f3) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 59), (2, 63), (3, 68), (4, 4), (5, 61), (9, 9), (12, 66), (13, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1080f6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 59), (2, 63), (3, 68), (4, 4), (5, 61), (9, 9), (12, 66), (13, 70), (14, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1080fe) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 59), (2, 63), (3, 68), (4, 4), (5, 61), (9, 9), (12, 66), (13, 70), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108106) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 53), (1, 59), (2, 63), (3, 68), (4, 4), (5, 61), (9, 9), (12, 66), (13, 70), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108110) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 77) (by decide) rfl

theorem block_l1080c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1080c0 :=
  Rest.liftedBlock (rest_l1080c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1080c0 x hx)

theorem rest_l108110 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108110 bytes_l108110) (entryMap (live .l108110))
      15 0x108110 bytes_l108110 b_l108110 := by
  have f0 : InstrSpec 0x108110 [0x41, 0x8B, 0x41, 0x10] (LoadPre 0x108110 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x108110 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x108110 0 (.base 9 (.d8 0x10)))
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR32M32Effect_footprint 0x108110 0 (.base 9 (.d8 0x10))).toInstrSpec (mov_r32_m32_effect_step 0x108110 0x41 (by decide) 0 (.base 9 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x108114 [0x49, 0x8B, 0x09] (LoadPre 0x108114 (fun s => AddrMode.addr (.base 9 .none) s (0x108114 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x108114 1 (.base 9 .none))
      [.gpr 9] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x108114 1 (.base 9 .none)).toInstrSpec (mov_r64_m64_effect_step 0x108114 0x49 (by decide) 1 (.base 9 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x108117 [0x41, 0x8B, 0x51, 0x08] (LoadPre 0x108117 (fun s => AddrMode.addr (.base 9 (.d8 0x8)) s (0x108117 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x108117 2 (.base 9 (.d8 0x8)))
      [.gpr 9] [] [.reg 2, .rip] :=
    (movR32M32Effect_footprint 0x108117 2 (.base 9 (.d8 0x8))).toInstrSpec (mov_r32_m32_effect_step 0x108117 0x41 (by decide) 2 (.base 9 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10811b [0x41, 0x8B, 0x71, 0x0C] (LoadPre 0x10811b (fun s => AddrMode.addr (.base 9 (.d8 0xc)) s (0x10811b + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x10811b 6 (.base 9 (.d8 0xc)))
      [.gpr 9] [] [.reg 6, .rip] :=
    (movR32M32Effect_footprint 0x10811b 6 (.base 9 (.d8 0xc))).toInstrSpec (mov_r32_m32_effect_step 0x10811b 0x41 (by decide) 6 (.base 9 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10811f [0x01, 0xC6] (fun s => s.RIP = 0x10811f) (addR32R32Effect 0x10811f 2 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10811f 2 6 0).toInstrSpec (add_r32_r32_effect_step 0x10811f 0xc6 (by decide)) pre_rip
  have f5 : InstrSpec 0x108121 [0x0F, 0xCE] (fun s => s.RIP = 0x108121) (bswapR32Effect 0x108121 2 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (bswapR32Effect_footprint 0x108121 2 6).toInstrSpec (bswap_r32_effect_step 0x108121 0xce (by decide)) pre_rip
  have f6 : InstrSpec 0x108123 [0xFF, 0xC0] (fun s => s.RIP = 0x108123) (incR32Effect 0x108123 2 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (incR32Effect_footprint 0x108123 2 0).toInstrSpec (inc_r32_effect_step 0x108123 0xc0 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x108125 [0x41, 0x89, 0x41, 0x10] (StorePre 0x108125 4 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x108125 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x108125 0 (.base 9 (.d8 0x10)))
      [.gpr 0, .gpr 9] [] [.rip] :=
    (movM32R32Effect_footprint 0x108125 0 (.base 9 (.d8 0x10))).toInstrSpec (mov_m32_r32_effect_step 0x108125 0x41 (by decide) 0 (.base 9 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x108129 [0x48, 0x89, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x108129 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x108129 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108129 1 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108129 1 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m64_r64_effect_step 0x108129 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x108131 [0x89, 0x94, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x108131 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x108131 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108131 2 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x108131 2 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m32_r32_low_effect_step 0x108131 2 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x108138 [0x89, 0xB4, 0x24, 0x0C, 0x01, 0x00, 0x00] (StorePre 0x108138 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10c)) s (0x108138 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108138 6 (.sib 4 none 0 (.d32 0x10c)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x108138 6 (.sib 4 none 0 (.d32 0x10c))).toInstrSpec (mov_m32_r32_low_effect_step 0x108138 6 (.sib 4 none 0 (.d32 0x10c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x10813f [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10813f) (movR64R64Effect 0x10813f 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10813f 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10813f 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x108142 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x108142) (movR64R64Effect 0x108142 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x108142 6 3).toInstrSpec (mov_r64_r64_effect_step 0x108142 0x48 0xde (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x108145 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x108145) (movR64R64Effect 0x108145 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x108145 2 15).toInstrSpec (mov_r64_r64_effect_step 0x108145 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x108148 [0xE8, 0xB3, 0xCF, 0xFF, 0xFF] (PushPre 0x108148 5) (callEffect (fun _ => 0x105100) 0x10814d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x108148 0x105100 0x10814d).toInstrSpec (call_rel32_effect_step 0x108148 0xffffcfb3 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108114) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108117) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10811b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10811f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 61), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108121) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108123) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108125) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108129) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 65), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108131) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 65), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108138) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10813f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 65), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 71), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108142) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 65), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108145) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 65), (1, 55), (2, 75), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108148) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 65), (1, 55), (2, 75), (3, 3), (4, 77), (5, 5), (6, 73), (7, 71), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105100) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 79) (by decide) (by decide) rfl rfl

theorem block_l108110 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108110 :=
  Rest.liftedBlock (rest_l108110 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108110 x hx)

theorem rest_l10814d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10814d bytes_l10814d) (entryMap (live .l10814d))
      8 0x10814d bytes_l10814d b_l10814d := by
  have f0 : InstrSpec 0x10814d [0x4C, 0x8B, 0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00] (LoadPre 0x10814d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10814d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10814d 9 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x10814d 9 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_r64_m64_effect_step 0x10814d 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x108155 [0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x108155 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x108155 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108155 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108155 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x108155 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10815d [0x48, 0x8B, 0x8C, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x10815d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10815d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10815d 1 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10815d 1 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x10815d 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x108165 [0x4A, 0x89, 0x4C, 0x2C, 0x10] (StorePre 0x108165 5 (fun s => AddrMode.addr (.sib 4 (some 13) 0 (.d8 0x10)) s (0x108165 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108165 1 (.sib 4 (some 13) 0 (.d8 0x10)))
      [.gpr 1, .gpr 4, .gpr 13] [] [.rip] :=
    (movM64R64Effect_footprint 0x108165 1 (.sib 4 (some 13) 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x108165 0x4a (by decide) 1 (.sib 4 (some 13) 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10816a [0x4A, 0x89, 0x44, 0x2C, 0x08] (StorePre 0x10816a 5 (fun s => AddrMode.addr (.sib 4 (some 13) 0 (.d8 0x8)) s (0x10816a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10816a 0 (.sib 4 (some 13) 0 (.d8 0x8)))
      [.gpr 0, .gpr 4, .gpr 13] [] [.rip] :=
    (movM64R64Effect_footprint 0x10816a 0 (.sib 4 (some 13) 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10816a 0x4a (by decide) 0 (.sib 4 (some 13) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10816f [0x49, 0x83, 0xC5, 0x10] (fun s => s.RIP = 0x10816f) (addR64Imm8Effect 0x10816f 13 0x10)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10816f 13 0x10).toInstrSpec (add_r64_imm8_effect_step 0x10816f 0x49 0xc5 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x108173 [0x4D, 0x39, 0xEC] (fun s => s.RIP = 0x108173) (cmpR64R64Effect 0x108173 12 13)
      [.gpr 12, .gpr 13] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x108173 12 13).toInstrSpec (cmp_r64_r64_effect_step 0x108173 0x4d 0xec (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108155) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10815d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108165) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10816a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10816f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108173) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 61), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108176) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 65) (jcc_rel8_effect_step 0x108176 5 0x98) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10814d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10814d :=
  Rest.liftedBlock (rest_l10814d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10814d x hx)

theorem rest_l108178_3 [Bindings] (code : CodeMap) :
    Rest (n := 153) code lifted (codeRange 0x108178 bytes_l108178) [(0, 149), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (19, 151), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x108293 bytes_l108178_3 b_l108178_3 := by
  exact Rest.jcc (n := 153) (jcc_rel32_effect_step 0x108293 4 0x228) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l108178_2 [Bindings] (code : CodeMap) :
    Rest (n := 128) code lifted (codeRange 0x108178 bytes_l108178) [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 125), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]
      21 0x108239 bytes_l108178_2 b_l108178_2 := by
  have f40 : InstrSpec 0x108239 [0x0F, 0xB6, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x108239 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x108239 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108239 8 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x108239 8 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (movzx_r32_m8_effect_step 0x108239 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x108241 [0x40, 0x88, 0x70, 0x01] (StorePre 0x108241 4 (fun s => AddrMode.addr (.base 0 (.d8 0x1)) s (0x108241 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108241 4 6 (.base 0 (.d8 0x1)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x108241 4 6 (.base 0 (.d8 0x1))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108241 0x40 (by decide) 6 (.base 0 (.d8 0x1)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x108245 [0x0F, 0xB6, 0x74, 0x24, 0x78] (LoadPre 0x108245 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x108245 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108245 5 6 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x108245 5 6 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (movzx_r32_m8_effect_step 0x108245 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f43 : InstrSpec 0x10824a [0x40, 0x88, 0x70, 0x02] (StorePre 0x10824a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2)) s (0x10824a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10824a 4 6 (.base 0 (.d8 0x2)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10824a 4 6 (.base 0 (.d8 0x2))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10824a 0x40 (by decide) 6 (.base 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f44 : InstrSpec 0x10824e [0x0F, 0xB6, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x10824e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10824e + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10824e 8 6 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x10824e 8 6 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (movzx_r32_m8_effect_step 0x10824e 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f45 : InstrSpec 0x108256 [0x40, 0x88, 0x70, 0x03] (StorePre 0x108256 4 (fun s => AddrMode.addr (.base 0 (.d8 0x3)) s (0x108256 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108256 4 6 (.base 0 (.d8 0x3)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x108256 4 6 (.base 0 (.d8 0x3))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108256 0x40 (by decide) 6 (.base 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f46 : InstrSpec 0x10825a [0x40, 0x88, 0x78, 0x04] (StorePre 0x10825a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x10825a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10825a 4 7 (.base 0 (.d8 0x4)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10825a 4 7 (.base 0 (.d8 0x4))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10825a 0x40 (by decide) 7 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f47 : InstrSpec 0x10825e [0x44, 0x88, 0x40, 0x05] (StorePre 0x10825e 4 (fun s => AddrMode.addr (.base 0 (.d8 0x5)) s (0x10825e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10825e 4 8 (.base 0 (.d8 0x5)))
      [.gpr 8, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10825e 4 8 (.base 0 (.d8 0x5))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10825e 0x44 (by decide) 0 (.base 0 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x108262 [0x44, 0x88, 0x48, 0x06] (StorePre 0x108262 4 (fun s => AddrMode.addr (.base 0 (.d8 0x6)) s (0x108262 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108262 4 9 (.base 0 (.d8 0x6)))
      [.gpr 9, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x108262 4 9 (.base 0 (.d8 0x6))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108262 0x44 (by decide) 1 (.base 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x108266 [0x44, 0x88, 0x50, 0x07] (StorePre 0x108266 4 (fun s => AddrMode.addr (.base 0 (.d8 0x7)) s (0x108266 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108266 4 10 (.base 0 (.d8 0x7)))
      [.gpr 10, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x108266 4 10 (.base 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108266 0x44 (by decide) 2 (.base 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f50 : InstrSpec 0x10826a [0x44, 0x88, 0x58, 0x08] (StorePre 0x10826a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x10826a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10826a 4 11 (.base 0 (.d8 0x8)))
      [.gpr 11, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10826a 4 11 (.base 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10826a 0x44 (by decide) 3 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f51 : InstrSpec 0x10826e [0x88, 0x58, 0x09] (StorePre 0x10826e 3 (fun s => AddrMode.addr (.base 0 (.d8 0x9)) s (0x10826e + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10826e 3 3 (.base 0 (.d8 0x9)))
      [.gpr 3, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10826e 3 3 (.base 0 (.d8 0x9))).toInstrSpec (mov_m8_r8_effect_step 0x10826e 3 (by decide) (.base 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x108271 [0x40, 0x88, 0x68, 0x0A] (StorePre 0x108271 4 (fun s => AddrMode.addr (.base 0 (.d8 0xa)) s (0x108271 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108271 4 5 (.base 0 (.d8 0xa)))
      [.gpr 5, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x108271 4 5 (.base 0 (.d8 0xa))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108271 0x40 (by decide) 5 (.base 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f53 : InstrSpec 0x108275 [0x44, 0x88, 0x70, 0x0B] (StorePre 0x108275 4 (fun s => AddrMode.addr (.base 0 (.d8 0xb)) s (0x108275 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108275 4 14 (.base 0 (.d8 0xb)))
      [.gpr 14, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x108275 4 14 (.base 0 (.d8 0xb))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108275 0x44 (by decide) 6 (.base 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x108279 [0x44, 0x88, 0x78, 0x0C] (StorePre 0x108279 4 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x108279 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108279 4 15 (.base 0 (.d8 0xc)))
      [.gpr 15, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x108279 4 15 (.base 0 (.d8 0xc))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108279 0x44 (by decide) 7 (.base 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f55 : InstrSpec 0x10827d [0x44, 0x88, 0x60, 0x0D] (StorePre 0x10827d 4 (fun s => AddrMode.addr (.base 0 (.d8 0xd)) s (0x10827d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10827d 4 12 (.base 0 (.d8 0xd)))
      [.gpr 12, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10827d 4 12 (.base 0 (.d8 0xd))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10827d 0x44 (by decide) 4 (.base 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x108281 [0x44, 0x88, 0x68, 0x0E] (StorePre 0x108281 4 (fun s => AddrMode.addr (.base 0 (.d8 0xe)) s (0x108281 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108281 4 13 (.base 0 (.d8 0xe)))
      [.gpr 13, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x108281 4 13 (.base 0 (.d8 0xe))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108281 0x44 (by decide) 5 (.base 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f57 : InstrSpec 0x108285 [0x88, 0x48, 0x0F] (StorePre 0x108285 3 (fun s => AddrMode.addr (.base 0 (.d8 0xf)) s (0x108285 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108285 3 1 (.base 0 (.d8 0xf)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x108285 3 1 (.base 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_effect_step 0x108285 1 (by decide) (.base 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f58 : InstrSpec 0x108288 [0x48, 0x8B, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00] (LoadPre 0x108288 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x108288 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108288 0 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108288 0 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_r64_m64_effect_step 0x108288 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f59 : InstrSpec 0x108290 [0x83, 0xF8, 0x01] (fun s => s.RIP = 0x108290) (cmpR32Imm8Effect 0x108290 3 0 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x108290 3 0 0x1).toInstrSpec (cmp_r32_imm8_effect_step 0x108290 0xf8 0x1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f40 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 128), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108241) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.exec (n := 130) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 128), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108245) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f42 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 131), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10824a) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.exec (n := 133) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 131), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10824e) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f44 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108256) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.exec (n := 136) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10825a) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 137) (RestInside.exec (n := 137) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10825e) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 138) (RestInside.exec (n := 138) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108262) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 139) (RestInside.exec (n := 139) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108266) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 140) (RestInside.exec (n := 140) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10826a) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 141) (RestInside.exec (n := 141) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10826e) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 142) (RestInside.exec (n := 142) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108271) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 143) (RestInside.exec (n := 143) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108275) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 144) (RestInside.exec (n := 144) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108279) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 145) (RestInside.exec (n := 145) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10827d) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 146) (RestInside.exec (n := 146) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108281) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 147) (RestInside.exec (n := 147) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108285) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 148) (RestInside.exec (n := 148) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108288) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f58 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 149), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108290) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f59 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 149), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (19, 151), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108293) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l108178_3 code

theorem rest_l108178_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x108178 bytes_l108178) [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (10, 87), (22, 22), (39, 39), (50, 50), (51, 51)]
      41 0x1081d8 bytes_l108178_1 b_l108178_1 := by
  have f20 : InstrSpec 0x1081d8 [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x10] (LoadPre 0x1081d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1081d8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1081d8 6 11 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x1081d8 6 11 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1081d8 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x1081de [0x44, 0x32, 0x5D, 0x08] (LoadPre 0x1081de (fun s => AddrMode.addr (.base 5 (.d8 0x8)) s (0x1081de + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1081de 4 11 (.base 5 (.d8 0x8)))
      [.gpr 11, .gpr 5] [] [.reg 11, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1081de 4 11 (.base 5 (.d8 0x8))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1081de 0x44 (by decide) 3 (.base 5 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x1081e2 [0x0F, 0xB6, 0x5C, 0x24, 0x11] (LoadPre 0x1081e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x1081e2 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1081e2 5 3 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x1081e2 5 3 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (movzx_r32_m8_effect_step 0x1081e2 3 (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x1081e7 [0x32, 0x5D, 0x09] (LoadPre 0x1081e7 (fun s => AddrMode.addr (.base 5 (.d8 0x9)) s (0x1081e7 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1081e7 3 3 (.base 5 (.d8 0x9)))
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1081e7 3 3 (.base 5 (.d8 0x9))).toInstrSpec (xor_r8_m8_effect_step 0x1081e7 3 (by decide) (.base 5 (.d8 0x9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x1081ea [0x48, 0x89, 0xEA] (fun s => s.RIP = 0x1081ea) (movR64R64Effect 0x1081ea 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1081ea 2 5).toInstrSpec (mov_r64_r64_effect_step 0x1081ea 0x48 0xea (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x1081ed [0x0F, 0xB6, 0x6C, 0x24, 0x12] (LoadPre 0x1081ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x1081ed + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1081ed 5 5 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x1081ed 5 5 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (movzx_r32_m8_effect_step 0x1081ed 5 (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x1081f2 [0x40, 0x32, 0x6A, 0x0A] (LoadPre 0x1081f2 (fun s => AddrMode.addr (.base 2 (.d8 0xa)) s (0x1081f2 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1081f2 4 5 (.base 2 (.d8 0xa)))
      [.gpr 5, .gpr 2] [] [.reg 5, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1081f2 4 5 (.base 2 (.d8 0xa))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1081f2 0x40 (by decide) 5 (.base 2 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x1081f6 [0x44, 0x0F, 0xB6, 0x74, 0x24, 0x13] (LoadPre 0x1081f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x1081f6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1081f6 6 14 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x1081f6 6 14 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1081f6 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x1081fc [0x44, 0x32, 0x72, 0x0B] (LoadPre 0x1081fc (fun s => AddrMode.addr (.base 2 (.d8 0xb)) s (0x1081fc + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1081fc 4 14 (.base 2 (.d8 0xb)))
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1081fc 4 14 (.base 2 (.d8 0xb))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1081fc 0x44 (by decide) 6 (.base 2 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x108200 [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x14] (LoadPre 0x108200 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x108200 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108200 6 15 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x108200 6 15 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108200 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x108206 [0x44, 0x32, 0x7A, 0x0C] (LoadPre 0x108206 (fun s => AddrMode.addr (.base 2 (.d8 0xc)) s (0x108206 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108206 4 15 (.base 2 (.d8 0xc)))
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108206 4 15 (.base 2 (.d8 0xc))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108206 0x44 (by decide) 7 (.base 2 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x10820a [0x44, 0x0F, 0xB6, 0x64, 0x24, 0x15] (LoadPre 0x10820a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x10820a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10820a 6 12 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x10820a 6 12 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10820a 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x108210 [0x44, 0x32, 0x62, 0x0D] (LoadPre 0x108210 (fun s => AddrMode.addr (.base 2 (.d8 0xd)) s (0x108210 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108210 4 12 (.base 2 (.d8 0xd)))
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108210 4 12 (.base 2 (.d8 0xd))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108210 0x44 (by decide) 4 (.base 2 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x108214 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x16] (LoadPre 0x108214 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x108214 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108214 6 13 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108214 6 13 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108214 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f34 : InstrSpec 0x10821a [0x44, 0x32, 0x6A, 0x0E] (LoadPre 0x10821a (fun s => AddrMode.addr (.base 2 (.d8 0xe)) s (0x10821a + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10821a 4 13 (.base 2 (.d8 0xe)))
      [.gpr 13, .gpr 2] [] [.reg 13, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10821a 4 13 (.base 2 (.d8 0xe))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10821a 0x44 (by decide) 5 (.base 2 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x10821e [0x0F, 0xB6, 0x4C, 0x24, 0x17] (LoadPre 0x10821e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x10821e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10821e 5 1 (.sib 4 none 0 (.d8 0x17)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10821e 5 1 (.sib 4 none 0 (.d8 0x17))).toInstrSpec (movzx_r32_m8_effect_step 0x10821e 1 (.sib 4 none 0 (.d8 0x17)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x108223 [0x32, 0x4A, 0x0F] (LoadPre 0x108223 (fun s => AddrMode.addr (.base 2 (.d8 0xf)) s (0x108223 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x108223 3 1 (.base 2 (.d8 0xf)))
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108223 3 1 (.base 2 (.d8 0xf))).toInstrSpec (xor_r8_m8_effect_step 0x108223 1 (by decide) (.base 2 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x108226 [0x48, 0x8B, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x108226 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x108226 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108226 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108226 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x108226 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f38 : InstrSpec 0x10822e [0x0F, 0xB6, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x10822e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10822e + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10822e 8 6 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x10822e 8 6 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (movzx_r32_m8_effect_step 0x10822e 6 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x108236 [0x40, 0x88, 0x30] (StorePre 0x108236 3 (fun s => AddrMode.addr (.base 0 .none) s (0x108236 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108236 3 6 (.base 0 .none))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x108236 3 6 (.base 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x108236 0x40 (by decide) 6 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f20 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (10, 87), (11, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081de) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f21 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081e2) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f22 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 70), (1, 60), (3, 93), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081e7) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f23 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 70), (1, 60), (3, 95), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081ea) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f24 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081ed) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f25 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 99), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081f2) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f26 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081f6) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f27 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (14, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081fc) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f28 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (14, 105), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108200) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f29 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (14, 105), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108206) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f30 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10820a) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f31 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108210) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f32 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108214) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f33 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 115), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10821a) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f34 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 70), (1, 60), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10821e) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f35 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 70), (1, 119), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108223) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 70), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108226) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10822e) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f38 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 125), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108236) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.exec (n := 127) (ρ' := [(0, 123), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 125), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108239) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l108178_2 code

theorem rest_l108178 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108178 bytes_l108178) (entryMap (live .l108178))
      61 0x108178 bytes_l108178 b_l108178 := by
  have f0 : InstrSpec 0x108178 [0x0F, 0xB6, 0x44, 0x24, 0x08] (LoadPre 0x108178 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108178 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108178 5 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x108178 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x108178 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10817d [0x0F, 0xB6, 0x4C, 0x24, 0x09] (LoadPre 0x10817d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x10817d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10817d 5 1 (.sib 4 none 0 (.d8 0x9)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10817d 5 1 (.sib 4 none 0 (.d8 0x9))).toInstrSpec (movzx_r32_m8_effect_step 0x10817d 1 (.sib 4 none 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x108182 [0x32, 0x45, 0x00] (LoadPre 0x108182 (fun s => AddrMode.addr (.base 5 (.d8 0x0)) s (0x108182 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x108182 3 0 (.base 5 (.d8 0x0)))
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108182 3 0 (.base 5 (.d8 0x0))).toInstrSpec (xor_r8_m8_effect_step 0x108182 0 (by decide) (.base 5 (.d8 0x0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x108185 [0x88, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x108185 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x108185 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x108185 7 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108185 7 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m8_r8_effect_step 0x108185 0 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10818c [0x32, 0x4D, 0x01] (LoadPre 0x10818c (fun s => AddrMode.addr (.base 5 (.d8 0x1)) s (0x10818c + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10818c 3 1 (.base 5 (.d8 0x1)))
      [.gpr 1, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10818c 3 1 (.base 5 (.d8 0x1))).toInstrSpec (xor_r8_m8_effect_step 0x10818c 1 (by decide) (.base 5 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10818f [0x88, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x10818f 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10818f + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10818f 7 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10818f 7 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m8_r8_effect_step 0x10818f 1 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x108196 [0x0F, 0xB6, 0x44, 0x24, 0x0A] (LoadPre 0x108196 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x108196 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108196 5 0 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x108196 5 0 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (movzx_r32_m8_effect_step 0x108196 0 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10819b [0x32, 0x45, 0x02] (LoadPre 0x10819b (fun s => AddrMode.addr (.base 5 (.d8 0x2)) s (0x10819b + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10819b 3 0 (.base 5 (.d8 0x2)))
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10819b 3 0 (.base 5 (.d8 0x2))).toInstrSpec (xor_r8_m8_effect_step 0x10819b 0 (by decide) (.base 5 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10819e [0x88, 0x44, 0x24, 0x78] (StorePre 0x10819e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10819e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10819e 4 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10819e 4 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m8_r8_effect_step 0x10819e 0 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1081a2 [0x0F, 0xB6, 0x44, 0x24, 0x0B] (LoadPre 0x1081a2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1081a2 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1081a2 5 0 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1081a2 5 0 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (movzx_r32_m8_effect_step 0x1081a2 0 (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1081a7 [0x32, 0x45, 0x03] (LoadPre 0x1081a7 (fun s => AddrMode.addr (.base 5 (.d8 0x3)) s (0x1081a7 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1081a7 3 0 (.base 5 (.d8 0x3)))
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1081a7 3 0 (.base 5 (.d8 0x3))).toInstrSpec (xor_r8_m8_effect_step 0x1081a7 0 (by decide) (.base 5 (.d8 0x3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1081aa [0x88, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x1081aa 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1081aa + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1081aa 7 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1081aa 7 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m8_r8_effect_step 0x1081aa 0 (by decide) (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1081b1 [0x0F, 0xB6, 0x7C, 0x24, 0x0C] (LoadPre 0x1081b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1081b1 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1081b1 5 7 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x1081b1 5 7 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x1081b1 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1081b6 [0x40, 0x32, 0x7D, 0x04] (LoadPre 0x1081b6 (fun s => AddrMode.addr (.base 5 (.d8 0x4)) s (0x1081b6 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1081b6 4 7 (.base 5 (.d8 0x4)))
      [.gpr 7, .gpr 5] [] [.reg 7, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1081b6 4 7 (.base 5 (.d8 0x4))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1081b6 0x40 (by decide) 7 (.base 5 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1081ba [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x0D] (LoadPre 0x1081ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x1081ba + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1081ba 6 8 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x1081ba 6 8 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1081ba 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1081c0 [0x44, 0x32, 0x45, 0x05] (LoadPre 0x1081c0 (fun s => AddrMode.addr (.base 5 (.d8 0x5)) s (0x1081c0 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1081c0 4 8 (.base 5 (.d8 0x5)))
      [.gpr 8, .gpr 5] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1081c0 4 8 (.base 5 (.d8 0x5))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1081c0 0x44 (by decide) 0 (.base 5 (.d8 0x5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x1081c4 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x0E] (LoadPre 0x1081c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x1081c4 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1081c4 6 9 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x1081c4 6 9 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1081c4 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x1081ca [0x44, 0x32, 0x4D, 0x06] (LoadPre 0x1081ca (fun s => AddrMode.addr (.base 5 (.d8 0x6)) s (0x1081ca + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1081ca 4 9 (.base 5 (.d8 0x6)))
      [.gpr 9, .gpr 5] [] [.reg 9, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1081ca 4 9 (.base 5 (.d8 0x6))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1081ca 0x44 (by decide) 1 (.base 5 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x1081ce [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x0F] (LoadPre 0x1081ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1081ce + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1081ce 6 10 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x1081ce 6 10 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1081ce 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x1081d4 [0x44, 0x32, 0x55, 0x07] (LoadPre 0x1081d4 (fun s => AddrMode.addr (.base 5 (.d8 0x7)) s (0x1081d4 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1081d4 4 10 (.base 5 (.d8 0x7)))
      [.gpr 10, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1081d4 4 10 (.base 5 (.d8 0x7))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1081d4 0x44 (by decide) 2 (.base 5 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10817d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108182) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108185) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 57), (1, 55), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10818c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 57), (1, 60), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10818f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 60), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108196) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 60), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10819b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 60), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10819e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (1, 60), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081a2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 60), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081a7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081aa) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081b1) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081b6) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081ba) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081c0) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081c4) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 79), (9, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081ca) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081ce) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (10, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081d4) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 70), (1, 60), (4, 4), (5, 5), (7, 75), (8, 79), (9, 83), (10, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1081d8) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l108178_1 code

theorem block_l108178 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108178 :=
  Rest.liftedBlock (rest_l108178 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108178 x hx)

theorem rest_l108299_3 [Bindings] (code : CodeMap) :
    Rest (n := 153) code lifted (codeRange 0x108299 bytes_l108299) [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (19, 151), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x1083c1 bytes_l108299_3 b_l108299_3 := by
  exact Rest.jcc (n := 153) (jcc_rel32_effect_step 0x1083c1 4 0xfa) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l108299_2 [Bindings] (code : CodeMap) :
    Rest (n := 128) code lifted (codeRange 0x108299 bytes_l108299) [(0, 119), (1, 126), (2, 2), (3, 95), (4, 4), (5, 99), (6, 123), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]
      21 0x108362 bytes_l108299_2 b_l108299_2 := by
  have f40 : InstrSpec 0x108362 [0x0F, 0xB6, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x108362 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x108362 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108362 8 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x108362 8 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (movzx_r32_m8_effect_step 0x108362 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x10836a [0x40, 0x88, 0x71, 0x11] (StorePre 0x10836a 4 (fun s => AddrMode.addr (.base 1 (.d8 0x11)) s (0x10836a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10836a 4 6 (.base 1 (.d8 0x11)))
      [.gpr 6, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x10836a 4 6 (.base 1 (.d8 0x11))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10836a 0x40 (by decide) 6 (.base 1 (.d8 0x11)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x10836e [0x48, 0x8B, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x10836e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10836e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10836e 1 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10836e 1 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x10836e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f43 : InstrSpec 0x108376 [0x0F, 0xB6, 0x74, 0x24, 0x78] (LoadPre 0x108376 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x108376 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108376 5 6 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x108376 5 6 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (movzx_r32_m8_effect_step 0x108376 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f44 : InstrSpec 0x10837b [0x40, 0x88, 0x71, 0x12] (StorePre 0x10837b 4 (fun s => AddrMode.addr (.base 1 (.d8 0x12)) s (0x10837b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10837b 4 6 (.base 1 (.d8 0x12)))
      [.gpr 6, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x10837b 4 6 (.base 1 (.d8 0x12))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10837b 0x40 (by decide) 6 (.base 1 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x10837f [0x0F, 0xB6, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x10837f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10837f + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10837f 8 6 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x10837f 8 6 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (movzx_r32_m8_effect_step 0x10837f 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f46 : InstrSpec 0x108387 [0x40, 0x88, 0x71, 0x13] (StorePre 0x108387 4 (fun s => AddrMode.addr (.base 1 (.d8 0x13)) s (0x108387 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108387 4 6 (.base 1 (.d8 0x13)))
      [.gpr 6, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x108387 4 6 (.base 1 (.d8 0x13))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108387 0x40 (by decide) 6 (.base 1 (.d8 0x13)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f47 : InstrSpec 0x10838b [0x40, 0x88, 0x79, 0x14] (StorePre 0x10838b 4 (fun s => AddrMode.addr (.base 1 (.d8 0x14)) s (0x10838b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10838b 4 7 (.base 1 (.d8 0x14)))
      [.gpr 7, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x10838b 4 7 (.base 1 (.d8 0x14))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10838b 0x40 (by decide) 7 (.base 1 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x10838f [0x44, 0x88, 0x41, 0x15] (StorePre 0x10838f 4 (fun s => AddrMode.addr (.base 1 (.d8 0x15)) s (0x10838f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10838f 4 8 (.base 1 (.d8 0x15)))
      [.gpr 8, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x10838f 4 8 (.base 1 (.d8 0x15))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10838f 0x44 (by decide) 0 (.base 1 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x108393 [0x44, 0x88, 0x49, 0x16] (StorePre 0x108393 4 (fun s => AddrMode.addr (.base 1 (.d8 0x16)) s (0x108393 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108393 4 9 (.base 1 (.d8 0x16)))
      [.gpr 9, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x108393 4 9 (.base 1 (.d8 0x16))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108393 0x44 (by decide) 1 (.base 1 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f50 : InstrSpec 0x108397 [0x44, 0x88, 0x51, 0x17] (StorePre 0x108397 4 (fun s => AddrMode.addr (.base 1 (.d8 0x17)) s (0x108397 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108397 4 10 (.base 1 (.d8 0x17)))
      [.gpr 10, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x108397 4 10 (.base 1 (.d8 0x17))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108397 0x44 (by decide) 2 (.base 1 (.d8 0x17)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f51 : InstrSpec 0x10839b [0x44, 0x88, 0x59, 0x18] (StorePre 0x10839b 4 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x10839b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10839b 4 11 (.base 1 (.d8 0x18)))
      [.gpr 11, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x10839b 4 11 (.base 1 (.d8 0x18))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10839b 0x44 (by decide) 3 (.base 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x10839f [0x88, 0x59, 0x19] (StorePre 0x10839f 3 (fun s => AddrMode.addr (.base 1 (.d8 0x19)) s (0x10839f + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10839f 3 3 (.base 1 (.d8 0x19)))
      [.gpr 3, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x10839f 3 3 (.base 1 (.d8 0x19))).toInstrSpec (mov_m8_r8_effect_step 0x10839f 3 (by decide) (.base 1 (.d8 0x19)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f53 : InstrSpec 0x1083a2 [0x40, 0x88, 0x69, 0x1A] (StorePre 0x1083a2 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1a)) s (0x1083a2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1083a2 4 5 (.base 1 (.d8 0x1a)))
      [.gpr 5, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x1083a2 4 5 (.base 1 (.d8 0x1a))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1083a2 0x40 (by decide) 5 (.base 1 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x1083a6 [0x44, 0x88, 0x71, 0x1B] (StorePre 0x1083a6 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1b)) s (0x1083a6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1083a6 4 14 (.base 1 (.d8 0x1b)))
      [.gpr 14, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x1083a6 4 14 (.base 1 (.d8 0x1b))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1083a6 0x44 (by decide) 6 (.base 1 (.d8 0x1b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f55 : InstrSpec 0x1083aa [0x44, 0x88, 0x79, 0x1C] (StorePre 0x1083aa 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1c)) s (0x1083aa + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1083aa 4 15 (.base 1 (.d8 0x1c)))
      [.gpr 15, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x1083aa 4 15 (.base 1 (.d8 0x1c))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1083aa 0x44 (by decide) 7 (.base 1 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x1083ae [0x44, 0x88, 0x61, 0x1D] (StorePre 0x1083ae 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1d)) s (0x1083ae + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1083ae 4 12 (.base 1 (.d8 0x1d)))
      [.gpr 12, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x1083ae 4 12 (.base 1 (.d8 0x1d))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1083ae 0x44 (by decide) 4 (.base 1 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f57 : InstrSpec 0x1083b2 [0x44, 0x88, 0x69, 0x1E] (StorePre 0x1083b2 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1e)) s (0x1083b2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1083b2 4 13 (.base 1 (.d8 0x1e)))
      [.gpr 13, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x1083b2 4 13 (.base 1 (.d8 0x1e))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1083b2 0x44 (by decide) 5 (.base 1 (.d8 0x1e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f58 : InstrSpec 0x1083b6 [0x88, 0x41, 0x1F] (StorePre 0x1083b6 3 (fun s => AddrMode.addr (.base 1 (.d8 0x1f)) s (0x1083b6 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1083b6 3 0 (.base 1 (.d8 0x1f)))
      [.gpr 0, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x1083b6 3 0 (.base 1 (.d8 0x1f))).toInstrSpec (mov_m8_r8_effect_step 0x1083b6 0 (by decide) (.base 1 (.d8 0x1f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f59 : InstrSpec 0x1083b9 [0x83, 0xBC, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x02] (LoadPre 0x1083b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1083b9 + BitVec.ofNat 64 8)) 4) (cmpMImm8Effect 0x1083b9 8 32 (.sib 4 none 0 (.d32 0xe8)) 0x2)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x1083b9 8 (.sib 4 none 0 (.d32 0xe8)) 0x2).toInstrSpec (cmp_m32_imm8_effect_step 0x1083b9 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide) 0x2) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f40 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 119), (1, 126), (2, 2), (3, 95), (4, 4), (5, 99), (6, 128), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10836a) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.exec (n := 130) (ρ' := [(0, 119), (1, 126), (2, 2), (3, 95), (4, 4), (5, 99), (6, 128), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10836e) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f42 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 128), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108376) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f43 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 133), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10837b) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.exec (n := 135) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 133), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10837f) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f45 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108387) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.exec (n := 138) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10838b) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 139) (RestInside.exec (n := 139) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10838f) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 140) (RestInside.exec (n := 140) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108393) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 141) (RestInside.exec (n := 141) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108397) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 142) (RestInside.exec (n := 142) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10839b) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 143) (RestInside.exec (n := 143) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10839f) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 144) (RestInside.exec (n := 144) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083a2) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 145) (RestInside.exec (n := 145) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083a6) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 146) (RestInside.exec (n := 146) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083aa) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 147) (RestInside.exec (n := 147) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083ae) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 148) (RestInside.exec (n := 148) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083b2) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 149) (RestInside.exec (n := 149) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083b6) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 150) (RestInside.exec (n := 150) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083b9) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f59 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (19, 151), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083c1) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l108299_3 code

theorem rest_l108299_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x108299 bytes_l108299) [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (22, 22), (39, 39), (50, 50), (51, 51)]
      41 0x1082fb bytes_l108299_1 b_l108299_1 := by
  have f20 : InstrSpec 0x1082fb [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x20] (LoadPre 0x1082fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1082fb + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1082fb 6 11 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x1082fb 6 11 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1082fb 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x108301 [0x44, 0x32, 0x5A, 0x18] (LoadPre 0x108301 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x108301 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108301 4 11 (.base 2 (.d8 0x18)))
      [.gpr 11, .gpr 2] [] [.reg 11, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108301 4 11 (.base 2 (.d8 0x18))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108301 0x44 (by decide) 3 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x108305 [0x0F, 0xB6, 0x5C, 0x24, 0x21] (LoadPre 0x108305 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x21)) s (0x108305 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108305 5 3 (.sib 4 none 0 (.d8 0x21)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x108305 5 3 (.sib 4 none 0 (.d8 0x21))).toInstrSpec (movzx_r32_m8_effect_step 0x108305 3 (.sib 4 none 0 (.d8 0x21)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x10830a [0x32, 0x5A, 0x19] (LoadPre 0x10830a (fun s => AddrMode.addr (.base 2 (.d8 0x19)) s (0x10830a + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10830a 3 3 (.base 2 (.d8 0x19)))
      [.gpr 3, .gpr 2] [] [.reg 3, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10830a 3 3 (.base 2 (.d8 0x19))).toInstrSpec (xor_r8_m8_effect_step 0x10830a 3 (by decide) (.base 2 (.d8 0x19)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x10830d [0x0F, 0xB6, 0x6C, 0x24, 0x22] (LoadPre 0x10830d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x10830d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10830d 5 5 (.sib 4 none 0 (.d8 0x22)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x10830d 5 5 (.sib 4 none 0 (.d8 0x22))).toInstrSpec (movzx_r32_m8_effect_step 0x10830d 5 (.sib 4 none 0 (.d8 0x22)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x108312 [0x40, 0x32, 0x6A, 0x1A] (LoadPre 0x108312 (fun s => AddrMode.addr (.base 2 (.d8 0x1a)) s (0x108312 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108312 4 5 (.base 2 (.d8 0x1a)))
      [.gpr 5, .gpr 2] [] [.reg 5, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108312 4 5 (.base 2 (.d8 0x1a))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108312 0x40 (by decide) 5 (.base 2 (.d8 0x1a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x108316 [0x44, 0x0F, 0xB6, 0x74, 0x24, 0x23] (LoadPre 0x108316 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x23)) s (0x108316 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108316 6 14 (.sib 4 none 0 (.d8 0x23)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x108316 6 14 (.sib 4 none 0 (.d8 0x23))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108316 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x23)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x10831c [0x44, 0x32, 0x72, 0x1B] (LoadPre 0x10831c (fun s => AddrMode.addr (.base 2 (.d8 0x1b)) s (0x10831c + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10831c 4 14 (.base 2 (.d8 0x1b)))
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10831c 4 14 (.base 2 (.d8 0x1b))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10831c 0x44 (by decide) 6 (.base 2 (.d8 0x1b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x108320 [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x24] (LoadPre 0x108320 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x108320 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108320 6 15 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x108320 6 15 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108320 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x108326 [0x44, 0x32, 0x7A, 0x1C] (LoadPre 0x108326 (fun s => AddrMode.addr (.base 2 (.d8 0x1c)) s (0x108326 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108326 4 15 (.base 2 (.d8 0x1c)))
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108326 4 15 (.base 2 (.d8 0x1c))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108326 0x44 (by decide) 7 (.base 2 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x10832a [0x44, 0x0F, 0xB6, 0x64, 0x24, 0x25] (LoadPre 0x10832a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x10832a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10832a 6 12 (.sib 4 none 0 (.d8 0x25)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x10832a 6 12 (.sib 4 none 0 (.d8 0x25))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10832a 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x108330 [0x44, 0x32, 0x62, 0x1D] (LoadPre 0x108330 (fun s => AddrMode.addr (.base 2 (.d8 0x1d)) s (0x108330 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108330 4 12 (.base 2 (.d8 0x1d)))
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108330 4 12 (.base 2 (.d8 0x1d))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108330 0x44 (by decide) 4 (.base 2 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x108334 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x26] (LoadPre 0x108334 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x108334 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108334 6 13 (.sib 4 none 0 (.d8 0x26)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108334 6 13 (.sib 4 none 0 (.d8 0x26))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108334 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x26)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x10833a [0x44, 0x32, 0x6A, 0x1E] (LoadPre 0x10833a (fun s => AddrMode.addr (.base 2 (.d8 0x1e)) s (0x10833a + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10833a 4 13 (.base 2 (.d8 0x1e)))
      [.gpr 13, .gpr 2] [] [.reg 13, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10833a 4 13 (.base 2 (.d8 0x1e))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10833a 0x44 (by decide) 5 (.base 2 (.d8 0x1e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f34 : InstrSpec 0x10833e [0x0F, 0xB6, 0x44, 0x24, 0x27] (LoadPre 0x10833e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x10833e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10833e 5 0 (.sib 4 none 0 (.d8 0x27)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10833e 5 0 (.sib 4 none 0 (.d8 0x27))).toInstrSpec (movzx_r32_m8_effect_step 0x10833e 0 (.sib 4 none 0 (.d8 0x27)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x108343 [0x32, 0x42, 0x1F] (LoadPre 0x108343 (fun s => AddrMode.addr (.base 2 (.d8 0x1f)) s (0x108343 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x108343 3 0 (.base 2 (.d8 0x1f)))
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108343 3 0 (.base 2 (.d8 0x1f))).toInstrSpec (xor_r8_m8_effect_step 0x108343 0 (by decide) (.base 2 (.d8 0x1f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x108346 [0x48, 0x8B, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x108346 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x108346 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108346 1 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x108346 1 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x108346 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x10834e [0x0F, 0xB6, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x10834e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10834e + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10834e 8 6 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x10834e 8 6 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (movzx_r32_m8_effect_step 0x10834e 6 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f38 : InstrSpec 0x108356 [0x40, 0x88, 0x71, 0x10] (StorePre 0x108356 4 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x108356 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108356 4 6 (.base 1 (.d8 0x10)))
      [.gpr 6, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x108356 4 6 (.base 1 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108356 0x40 (by decide) 6 (.base 1 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x10835a [0x48, 0x8B, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x10835a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10835a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10835a 1 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10835a 1 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x10835a 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f20 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108301) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f21 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108305) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f22 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(1, 70), (2, 2), (3, 93), (4, 4), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10830a) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f23 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10830d) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f24 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 97), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108312) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f25 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108316) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f26 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (14, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10831c) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f27 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (14, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108320) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f28 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (14, 103), (15, 105), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108326) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f29 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10832a) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f30 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 109), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108330) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f31 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108334) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f32 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 113), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10833a) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f33 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10833e) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f34 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 117), (1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108343) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f35 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 119), (1, 70), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108346) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 119), (1, 121), (2, 2), (3, 95), (4, 4), (5, 99), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10834e) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 119), (1, 121), (2, 2), (3, 95), (4, 4), (5, 99), (6, 123), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108356) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.exec (n := 125) (ρ' := [(0, 119), (1, 121), (2, 2), (3, 95), (4, 4), (5, 99), (6, 123), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10835a) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f39 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 119), (1, 126), (2, 2), (3, 95), (4, 4), (5, 99), (6, 123), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108362) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l108299_2 code

theorem rest_l108299 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108299 bytes_l108299) (entryMap (live .l108299))
      61 0x108299 bytes_l108299 b_l108299 := by
  have f0 : InstrSpec 0x108299 [0x0F, 0xB6, 0x4C, 0x24, 0x18] (LoadPre 0x108299 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x108299 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108299 5 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108299 5 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (movzx_r32_m8_effect_step 0x108299 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10829e [0x0F, 0xB6, 0x74, 0x24, 0x19] (LoadPre 0x10829e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x10829e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10829e 5 6 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x10829e 5 6 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (movzx_r32_m8_effect_step 0x10829e 6 (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1082a3 [0x32, 0x4A, 0x10] (LoadPre 0x1082a3 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1082a3 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1082a3 3 1 (.base 2 (.d8 0x10)))
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1082a3 3 1 (.base 2 (.d8 0x10))).toInstrSpec (xor_r8_m8_effect_step 0x1082a3 1 (by decide) (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1082a6 [0x88, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1082a6 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1082a6 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1082a6 7 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1082a6 7 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m8_r8_effect_step 0x1082a6 1 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1082ad [0x40, 0x32, 0x72, 0x11] (LoadPre 0x1082ad (fun s => AddrMode.addr (.base 2 (.d8 0x11)) s (0x1082ad + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1082ad 4 6 (.base 2 (.d8 0x11)))
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1082ad 4 6 (.base 2 (.d8 0x11))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1082ad 0x40 (by decide) 6 (.base 2 (.d8 0x11)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1082b1 [0x40, 0x88, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x1082b1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1082b1 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x1082b1 8 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1082b1 8 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1082b1 0x40 (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1082b9 [0x0F, 0xB6, 0x4C, 0x24, 0x1A] (LoadPre 0x1082b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x1082b9 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1082b9 5 1 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1082b9 5 1 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (movzx_r32_m8_effect_step 0x1082b9 1 (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1082be [0x32, 0x4A, 0x12] (LoadPre 0x1082be (fun s => AddrMode.addr (.base 2 (.d8 0x12)) s (0x1082be + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1082be 3 1 (.base 2 (.d8 0x12)))
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1082be 3 1 (.base 2 (.d8 0x12))).toInstrSpec (xor_r8_m8_effect_step 0x1082be 1 (by decide) (.base 2 (.d8 0x12)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1082c1 [0x88, 0x4C, 0x24, 0x78] (StorePre 0x1082c1 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1082c1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1082c1 4 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1082c1 4 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m8_r8_effect_step 0x1082c1 1 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1082c5 [0x0F, 0xB6, 0x4C, 0x24, 0x1B] (LoadPre 0x1082c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x1082c5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1082c5 5 1 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1082c5 5 1 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (movzx_r32_m8_effect_step 0x1082c5 1 (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1082ca [0x32, 0x4A, 0x13] (LoadPre 0x1082ca (fun s => AddrMode.addr (.base 2 (.d8 0x13)) s (0x1082ca + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1082ca 3 1 (.base 2 (.d8 0x13)))
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1082ca 3 1 (.base 2 (.d8 0x13))).toInstrSpec (xor_r8_m8_effect_step 0x1082ca 1 (by decide) (.base 2 (.d8 0x13)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1082cd [0x88, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x1082cd 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1082cd + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1082cd 7 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1082cd 7 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m8_r8_effect_step 0x1082cd 1 (by decide) (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1082d4 [0x0F, 0xB6, 0x7C, 0x24, 0x1C] (LoadPre 0x1082d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1082d4 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1082d4 5 7 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x1082d4 5 7 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (movzx_r32_m8_effect_step 0x1082d4 7 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1082d9 [0x40, 0x32, 0x7A, 0x14] (LoadPre 0x1082d9 (fun s => AddrMode.addr (.base 2 (.d8 0x14)) s (0x1082d9 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1082d9 4 7 (.base 2 (.d8 0x14)))
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1082d9 4 7 (.base 2 (.d8 0x14))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1082d9 0x40 (by decide) 7 (.base 2 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1082dd [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x1D] (LoadPre 0x1082dd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x1082dd + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1082dd 6 8 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x1082dd 6 8 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1082dd 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1082e3 [0x44, 0x32, 0x42, 0x15] (LoadPre 0x1082e3 (fun s => AddrMode.addr (.base 2 (.d8 0x15)) s (0x1082e3 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1082e3 4 8 (.base 2 (.d8 0x15)))
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1082e3 4 8 (.base 2 (.d8 0x15))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1082e3 0x44 (by decide) 0 (.base 2 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x1082e7 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x1E] (LoadPre 0x1082e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x1082e7 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1082e7 6 9 (.sib 4 none 0 (.d8 0x1e)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x1082e7 6 9 (.sib 4 none 0 (.d8 0x1e))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1082e7 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x1082ed [0x44, 0x32, 0x4A, 0x16] (LoadPre 0x1082ed (fun s => AddrMode.addr (.base 2 (.d8 0x16)) s (0x1082ed + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1082ed 4 9 (.base 2 (.d8 0x16)))
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1082ed 4 9 (.base 2 (.d8 0x16))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1082ed 0x44 (by decide) 1 (.base 2 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x1082f1 [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x1F] (LoadPre 0x1082f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x1082f1 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1082f1 6 10 (.sib 4 none 0 (.d8 0x1f)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x1082f1 6 10 (.sib 4 none 0 (.d8 0x1f))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1082f1 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x1082f7 [0x44, 0x32, 0x52, 0x17] (LoadPre 0x1082f7 (fun s => AddrMode.addr (.base 2 (.d8 0x17)) s (0x1082f7 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1082f7 4 10 (.base 2 (.d8 0x17)))
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1082f7 4 10 (.base 2 (.d8 0x17))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1082f7 0x44 (by decide) 2 (.base 2 (.d8 0x17)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10829e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 2), (4, 4), (6, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082a3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (2, 2), (4, 4), (6, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082a6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(1, 57), (2, 2), (4, 4), (6, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082ad) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 57), (2, 2), (4, 4), (6, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082b1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(1, 57), (2, 2), (4, 4), (6, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082b9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 63), (2, 2), (4, 4), (6, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082be) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 65), (2, 2), (4, 4), (6, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082c1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(1, 65), (2, 2), (4, 4), (6, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082c5) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 68), (2, 2), (4, 4), (6, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082ca) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082cd) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082d4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082d9) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082dd) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082e3) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082e7) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 79), (9, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082ed) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 79), (9, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082f1) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 79), (9, 83), (10, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082f7) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(1, 70), (2, 2), (4, 4), (6, 60), (7, 75), (8, 79), (9, 83), (10, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1082fb) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l108299_1 code

theorem block_l108299 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108299 :=
  Rest.liftedBlock (rest_l108299 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108299 x hx)

theorem rest_l1083c7_2 [Bindings] (code : CodeMap) :
    Rest (n := 128) code lifted (codeRange 0x1083c7 bytes_l1083c7) [(0, 55), (1, 120), (2, 125), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]
      15 0x108487 bytes_l1083c7_2 b_l1083c7_2 := by
  have f40 : InstrSpec 0x108487 [0x0F, 0xB6, 0x54, 0x24, 0x78] (LoadPre 0x108487 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x108487 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108487 5 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x108487 5 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (movzx_r32_m8_effect_step 0x108487 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x10848c [0x88, 0x50, 0x22] (StorePre 0x10848c 3 (fun s => AddrMode.addr (.base 0 (.d8 0x22)) s (0x10848c + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10848c 3 2 (.base 0 (.d8 0x22)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10848c 3 2 (.base 0 (.d8 0x22))).toInstrSpec (mov_m8_r8_effect_step 0x10848c 2 (by decide) (.base 0 (.d8 0x22)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x10848f [0x40, 0x88, 0x70, 0x23] (StorePre 0x10848f 4 (fun s => AddrMode.addr (.base 0 (.d8 0x23)) s (0x10848f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10848f 4 6 (.base 0 (.d8 0x23)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10848f 4 6 (.base 0 (.d8 0x23))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10848f 0x40 (by decide) 6 (.base 0 (.d8 0x23)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f43 : InstrSpec 0x108493 [0x40, 0x88, 0x78, 0x24] (StorePre 0x108493 4 (fun s => AddrMode.addr (.base 0 (.d8 0x24)) s (0x108493 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108493 4 7 (.base 0 (.d8 0x24)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x108493 4 7 (.base 0 (.d8 0x24))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108493 0x40 (by decide) 7 (.base 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f44 : InstrSpec 0x108497 [0x44, 0x88, 0x40, 0x25] (StorePre 0x108497 4 (fun s => AddrMode.addr (.base 0 (.d8 0x25)) s (0x108497 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108497 4 8 (.base 0 (.d8 0x25)))
      [.gpr 8, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x108497 4 8 (.base 0 (.d8 0x25))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108497 0x44 (by decide) 0 (.base 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x10849b [0x44, 0x88, 0x48, 0x26] (StorePre 0x10849b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x26)) s (0x10849b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10849b 4 9 (.base 0 (.d8 0x26)))
      [.gpr 9, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10849b 4 9 (.base 0 (.d8 0x26))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10849b 0x44 (by decide) 1 (.base 0 (.d8 0x26)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f46 : InstrSpec 0x10849f [0x44, 0x88, 0x50, 0x27] (StorePre 0x10849f 4 (fun s => AddrMode.addr (.base 0 (.d8 0x27)) s (0x10849f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10849f 4 10 (.base 0 (.d8 0x27)))
      [.gpr 10, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10849f 4 10 (.base 0 (.d8 0x27))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10849f 0x44 (by decide) 2 (.base 0 (.d8 0x27)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f47 : InstrSpec 0x1084a3 [0x44, 0x88, 0x58, 0x28] (StorePre 0x1084a3 4 (fun s => AddrMode.addr (.base 0 (.d8 0x28)) s (0x1084a3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1084a3 4 11 (.base 0 (.d8 0x28)))
      [.gpr 11, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x1084a3 4 11 (.base 0 (.d8 0x28))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1084a3 0x44 (by decide) 3 (.base 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x1084a7 [0x88, 0x58, 0x29] (StorePre 0x1084a7 3 (fun s => AddrMode.addr (.base 0 (.d8 0x29)) s (0x1084a7 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1084a7 3 3 (.base 0 (.d8 0x29)))
      [.gpr 3, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x1084a7 3 3 (.base 0 (.d8 0x29))).toInstrSpec (mov_m8_r8_effect_step 0x1084a7 3 (by decide) (.base 0 (.d8 0x29)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x1084aa [0x40, 0x88, 0x68, 0x2A] (StorePre 0x1084aa 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2a)) s (0x1084aa + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1084aa 4 5 (.base 0 (.d8 0x2a)))
      [.gpr 5, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x1084aa 4 5 (.base 0 (.d8 0x2a))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1084aa 0x40 (by decide) 5 (.base 0 (.d8 0x2a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f50 : InstrSpec 0x1084ae [0x44, 0x88, 0x70, 0x2B] (StorePre 0x1084ae 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2b)) s (0x1084ae + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1084ae 4 14 (.base 0 (.d8 0x2b)))
      [.gpr 14, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x1084ae 4 14 (.base 0 (.d8 0x2b))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1084ae 0x44 (by decide) 6 (.base 0 (.d8 0x2b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f51 : InstrSpec 0x1084b2 [0x44, 0x88, 0x78, 0x2C] (StorePre 0x1084b2 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2c)) s (0x1084b2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1084b2 4 15 (.base 0 (.d8 0x2c)))
      [.gpr 15, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x1084b2 4 15 (.base 0 (.d8 0x2c))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1084b2 0x44 (by decide) 7 (.base 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x1084b6 [0x44, 0x88, 0x60, 0x2D] (StorePre 0x1084b6 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2d)) s (0x1084b6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1084b6 4 12 (.base 0 (.d8 0x2d)))
      [.gpr 12, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x1084b6 4 12 (.base 0 (.d8 0x2d))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1084b6 0x44 (by decide) 4 (.base 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f53 : InstrSpec 0x1084ba [0x44, 0x88, 0x68, 0x2E] (StorePre 0x1084ba 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2e)) s (0x1084ba + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1084ba 4 13 (.base 0 (.d8 0x2e)))
      [.gpr 13, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x1084ba 4 13 (.base 0 (.d8 0x2e))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1084ba 0x44 (by decide) 5 (.base 0 (.d8 0x2e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x1084be [0x88, 0x48, 0x2F] (StorePre 0x1084be 3 (fun s => AddrMode.addr (.base 0 (.d8 0x2f)) s (0x1084be + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1084be 3 1 (.base 0 (.d8 0x2f)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x1084be 3 1 (.base 0 (.d8 0x2f))).toInstrSpec (mov_m8_r8_effect_step 0x1084be 1 (by decide) (.base 0 (.d8 0x2f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f40 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10848c) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.exec (n := 130) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10848f) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 131) (RestInside.exec (n := 131) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108493) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 132) (RestInside.exec (n := 132) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108497) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 133) (RestInside.exec (n := 133) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10849b) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 134) (RestInside.exec (n := 134) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10849f) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 135) (RestInside.exec (n := 135) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084a3) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 136) (RestInside.exec (n := 136) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084a7) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 137) (RestInside.exec (n := 137) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084aa) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 138) (RestInside.exec (n := 138) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084ae) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 139) (RestInside.exec (n := 139) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084b2) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 140) (RestInside.exec (n := 140) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084b6) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 141) (RestInside.exec (n := 141) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084ba) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 142) (RestInside.exec (n := 142) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084be) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 143) (RestInside.exec (n := 143) (ρ' := [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084c1) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 144) (by decide) rfl

theorem rest_l1083c7_1 [Bindings] (code : CodeMap) :
    Rest (n := 90) code lifted (codeRange 0x1083c7 bytes_l1083c7) [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (22, 22), (39, 39), (50, 50), (51, 51)]
      35 0x108426 bytes_l1083c7_1 b_l1083c7_1 := by
  have f20 : InstrSpec 0x108426 [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x30] (LoadPre 0x108426 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108426 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108426 6 11 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x108426 6 11 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108426 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x10842c [0x44, 0x32, 0x5A, 0x28] (LoadPre 0x10842c (fun s => AddrMode.addr (.base 2 (.d8 0x28)) s (0x10842c + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10842c 4 11 (.base 2 (.d8 0x28)))
      [.gpr 11, .gpr 2] [] [.reg 11, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10842c 4 11 (.base 2 (.d8 0x28))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10842c 0x44 (by decide) 3 (.base 2 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x108430 [0x0F, 0xB6, 0x5C, 0x24, 0x31] (LoadPre 0x108430 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x108430 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108430 5 3 (.sib 4 none 0 (.d8 0x31)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x108430 5 3 (.sib 4 none 0 (.d8 0x31))).toInstrSpec (movzx_r32_m8_effect_step 0x108430 3 (.sib 4 none 0 (.d8 0x31)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x108435 [0x32, 0x5A, 0x29] (LoadPre 0x108435 (fun s => AddrMode.addr (.base 2 (.d8 0x29)) s (0x108435 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x108435 3 3 (.base 2 (.d8 0x29)))
      [.gpr 3, .gpr 2] [] [.reg 3, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108435 3 3 (.base 2 (.d8 0x29))).toInstrSpec (xor_r8_m8_effect_step 0x108435 3 (by decide) (.base 2 (.d8 0x29)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x108438 [0x0F, 0xB6, 0x6C, 0x24, 0x32] (LoadPre 0x108438 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x108438 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108438 5 5 (.sib 4 none 0 (.d8 0x32)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x108438 5 5 (.sib 4 none 0 (.d8 0x32))).toInstrSpec (movzx_r32_m8_effect_step 0x108438 5 (.sib 4 none 0 (.d8 0x32)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x10843d [0x40, 0x32, 0x6A, 0x2A] (LoadPre 0x10843d (fun s => AddrMode.addr (.base 2 (.d8 0x2a)) s (0x10843d + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10843d 4 5 (.base 2 (.d8 0x2a)))
      [.gpr 5, .gpr 2] [] [.reg 5, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10843d 4 5 (.base 2 (.d8 0x2a))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10843d 0x40 (by decide) 5 (.base 2 (.d8 0x2a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x108441 [0x44, 0x0F, 0xB6, 0x74, 0x24, 0x33] (LoadPre 0x108441 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x33)) s (0x108441 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108441 6 14 (.sib 4 none 0 (.d8 0x33)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x108441 6 14 (.sib 4 none 0 (.d8 0x33))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108441 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x33)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x108447 [0x44, 0x32, 0x72, 0x2B] (LoadPre 0x108447 (fun s => AddrMode.addr (.base 2 (.d8 0x2b)) s (0x108447 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108447 4 14 (.base 2 (.d8 0x2b)))
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108447 4 14 (.base 2 (.d8 0x2b))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108447 0x44 (by decide) 6 (.base 2 (.d8 0x2b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x10844b [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x34] (LoadPre 0x10844b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x10844b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10844b 6 15 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x10844b 6 15 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10844b 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x108451 [0x44, 0x32, 0x7A, 0x2C] (LoadPre 0x108451 (fun s => AddrMode.addr (.base 2 (.d8 0x2c)) s (0x108451 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108451 4 15 (.base 2 (.d8 0x2c)))
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108451 4 15 (.base 2 (.d8 0x2c))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108451 0x44 (by decide) 7 (.base 2 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x108455 [0x44, 0x0F, 0xB6, 0x64, 0x24, 0x35] (LoadPre 0x108455 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x108455 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108455 6 12 (.sib 4 none 0 (.d8 0x35)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x108455 6 12 (.sib 4 none 0 (.d8 0x35))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108455 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x35)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x10845b [0x44, 0x32, 0x62, 0x2D] (LoadPre 0x10845b (fun s => AddrMode.addr (.base 2 (.d8 0x2d)) s (0x10845b + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10845b 4 12 (.base 2 (.d8 0x2d)))
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10845b 4 12 (.base 2 (.d8 0x2d))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10845b 0x44 (by decide) 4 (.base 2 (.d8 0x2d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x10845f [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x36] (LoadPre 0x10845f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x10845f + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10845f 6 13 (.sib 4 none 0 (.d8 0x36)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x10845f 6 13 (.sib 4 none 0 (.d8 0x36))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10845f 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x36)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x108465 [0x44, 0x32, 0x6A, 0x2E] (LoadPre 0x108465 (fun s => AddrMode.addr (.base 2 (.d8 0x2e)) s (0x108465 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108465 4 13 (.base 2 (.d8 0x2e)))
      [.gpr 13, .gpr 2] [] [.reg 13, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108465 4 13 (.base 2 (.d8 0x2e))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108465 0x44 (by decide) 5 (.base 2 (.d8 0x2e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f34 : InstrSpec 0x108469 [0x0F, 0xB6, 0x4C, 0x24, 0x37] (LoadPre 0x108469 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x37)) s (0x108469 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108469 5 1 (.sib 4 none 0 (.d8 0x37)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108469 5 1 (.sib 4 none 0 (.d8 0x37))).toInstrSpec (movzx_r32_m8_effect_step 0x108469 1 (.sib 4 none 0 (.d8 0x37)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x10846e [0x32, 0x4A, 0x2F] (LoadPre 0x10846e (fun s => AddrMode.addr (.base 2 (.d8 0x2f)) s (0x10846e + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10846e 3 1 (.base 2 (.d8 0x2f)))
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10846e 3 1 (.base 2 (.d8 0x2f))).toInstrSpec (xor_r8_m8_effect_step 0x10846e 1 (by decide) (.base 2 (.d8 0x2f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x108471 [0x0F, 0xB6, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x108471 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x108471 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108471 8 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x108471 8 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (movzx_r32_m8_effect_step 0x108471 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x108479 [0x88, 0x50, 0x20] (StorePre 0x108479 3 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x108479 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108479 3 2 (.base 0 (.d8 0x20)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x108479 3 2 (.base 0 (.d8 0x20))).toInstrSpec (mov_m8_r8_effect_step 0x108479 2 (by decide) (.base 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x10847c [0x0F, 0xB6, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x10847c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10847c + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10847c 8 2 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x10847c 8 2 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (movzx_r32_m8_effect_step 0x10847c 2 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x108484 [0x88, 0x50, 0x21] (StorePre 0x108484 3 (fun s => AddrMode.addr (.base 0 (.d8 0x21)) s (0x108484 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108484 3 2 (.base 0 (.d8 0x21)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x108484 3 2 (.base 0 (.d8 0x21))).toInstrSpec (mov_m8_r8_effect_step 0x108484 2 (by decide) (.base 0 (.d8 0x21)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f20 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10842c) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f21 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108430) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f22 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 94), (4, 4), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108435) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f23 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108438) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f24 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 98), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10843d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f25 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108441) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f26 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (14, 102), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108447) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f27 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (14, 104), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10844b) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f28 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (14, 104), (15, 106), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108451) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f29 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108455) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f30 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 110), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10845b) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f31 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10845f) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f32 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 114), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108465) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f33 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108469) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f34 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 55), (1, 118), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10846e) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f35 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 55), (1, 120), (2, 2), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108471) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f36 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 55), (1, 120), (2, 122), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108479) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.exec (n := 124) (ρ' := [(0, 55), (1, 120), (2, 122), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10847c) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f38 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 55), (1, 120), (2, 125), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108484) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.exec (n := 127) (ρ' := [(0, 55), (1, 120), (2, 125), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108487) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1083c7_2 code

theorem rest_l1083c7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1083c7 bytes_l1083c7) (entryMap (live .l1083c7))
      55 0x1083c7 bytes_l1083c7 b_l1083c7 := by
  have f0 : InstrSpec 0x1083c7 [0x0F, 0xB6, 0x74, 0x24, 0x28] (LoadPre 0x1083c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1083c7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1083c7 5 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x1083c7 5 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (movzx_r32_m8_effect_step 0x1083c7 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1083cc [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x1083cc) (movR64R64Effect 0x1083cc 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1083cc 0 1).toInstrSpec (mov_r64_r64_effect_step 0x1083cc 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1083cf [0x0F, 0xB6, 0x4C, 0x24, 0x29] (LoadPre 0x1083cf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x29)) s (0x1083cf + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1083cf 5 1 (.sib 4 none 0 (.d8 0x29)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1083cf 5 1 (.sib 4 none 0 (.d8 0x29))).toInstrSpec (movzx_r32_m8_effect_step 0x1083cf 1 (.sib 4 none 0 (.d8 0x29)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1083d4 [0x40, 0x32, 0x72, 0x20] (LoadPre 0x1083d4 (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x1083d4 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1083d4 4 6 (.base 2 (.d8 0x20)))
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1083d4 4 6 (.base 2 (.d8 0x20))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1083d4 0x40 (by decide) 6 (.base 2 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1083d8 [0x40, 0x88, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1083d8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1083d8 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x1083d8 8 6 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1083d8 8 6 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1083d8 0x40 (by decide) 6 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1083e0 [0x32, 0x4A, 0x21] (LoadPre 0x1083e0 (fun s => AddrMode.addr (.base 2 (.d8 0x21)) s (0x1083e0 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1083e0 3 1 (.base 2 (.d8 0x21)))
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1083e0 3 1 (.base 2 (.d8 0x21))).toInstrSpec (xor_r8_m8_effect_step 0x1083e0 1 (by decide) (.base 2 (.d8 0x21)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1083e3 [0x88, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x1083e3 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1083e3 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1083e3 7 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1083e3 7 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m8_r8_effect_step 0x1083e3 1 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1083ea [0x0F, 0xB6, 0x4C, 0x24, 0x2A] (LoadPre 0x1083ea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x1083ea + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1083ea 5 1 (.sib 4 none 0 (.d8 0x2a)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1083ea 5 1 (.sib 4 none 0 (.d8 0x2a))).toInstrSpec (movzx_r32_m8_effect_step 0x1083ea 1 (.sib 4 none 0 (.d8 0x2a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1083ef [0x32, 0x4A, 0x22] (LoadPre 0x1083ef (fun s => AddrMode.addr (.base 2 (.d8 0x22)) s (0x1083ef + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1083ef 3 1 (.base 2 (.d8 0x22)))
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1083ef 3 1 (.base 2 (.d8 0x22))).toInstrSpec (xor_r8_m8_effect_step 0x1083ef 1 (by decide) (.base 2 (.d8 0x22)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1083f2 [0x88, 0x4C, 0x24, 0x78] (StorePre 0x1083f2 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1083f2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1083f2 4 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1083f2 4 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m8_r8_effect_step 0x1083f2 1 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1083f6 [0x0F, 0xB6, 0x74, 0x24, 0x2B] (LoadPre 0x1083f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2b)) s (0x1083f6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1083f6 5 6 (.sib 4 none 0 (.d8 0x2b)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x1083f6 5 6 (.sib 4 none 0 (.d8 0x2b))).toInstrSpec (movzx_r32_m8_effect_step 0x1083f6 6 (.sib 4 none 0 (.d8 0x2b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1083fb [0x40, 0x32, 0x72, 0x23] (LoadPre 0x1083fb (fun s => AddrMode.addr (.base 2 (.d8 0x23)) s (0x1083fb + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1083fb 4 6 (.base 2 (.d8 0x23)))
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1083fb 4 6 (.base 2 (.d8 0x23))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1083fb 0x40 (by decide) 6 (.base 2 (.d8 0x23)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1083ff [0x0F, 0xB6, 0x7C, 0x24, 0x2C] (LoadPre 0x1083ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x1083ff + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1083ff 5 7 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x1083ff 5 7 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (movzx_r32_m8_effect_step 0x1083ff 7 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x108404 [0x40, 0x32, 0x7A, 0x24] (LoadPre 0x108404 (fun s => AddrMode.addr (.base 2 (.d8 0x24)) s (0x108404 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108404 4 7 (.base 2 (.d8 0x24)))
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108404 4 7 (.base 2 (.d8 0x24))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108404 0x40 (by decide) 7 (.base 2 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x108408 [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x2D] (LoadPre 0x108408 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x108408 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108408 6 8 (.sib 4 none 0 (.d8 0x2d)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x108408 6 8 (.sib 4 none 0 (.d8 0x2d))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108408 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x10840e [0x44, 0x32, 0x42, 0x25] (LoadPre 0x10840e (fun s => AddrMode.addr (.base 2 (.d8 0x25)) s (0x10840e + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10840e 4 8 (.base 2 (.d8 0x25)))
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x10840e 4 8 (.base 2 (.d8 0x25))).toInstrSpec (xor_r8_m8_rex_effect_step 0x10840e 0x44 (by decide) 0 (.base 2 (.d8 0x25)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x108412 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x2E] (LoadPre 0x108412 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2e)) s (0x108412 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108412 6 9 (.sib 4 none 0 (.d8 0x2e)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x108412 6 9 (.sib 4 none 0 (.d8 0x2e))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108412 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x2e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x108418 [0x44, 0x32, 0x4A, 0x26] (LoadPre 0x108418 (fun s => AddrMode.addr (.base 2 (.d8 0x26)) s (0x108418 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108418 4 9 (.base 2 (.d8 0x26)))
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108418 4 9 (.base 2 (.d8 0x26))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108418 0x44 (by decide) 1 (.base 2 (.d8 0x26)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x10841c [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x2F] (LoadPre 0x10841c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2f)) s (0x10841c + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10841c 6 10 (.sib 4 none 0 (.d8 0x2f)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x10841c 6 10 (.sib 4 none 0 (.d8 0x2f))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10841c 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x2f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x108422 [0x44, 0x32, 0x52, 0x27] (LoadPre 0x108422 (fun s => AddrMode.addr (.base 2 (.d8 0x27)) s (0x108422 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108422 4 10 (.base 2 (.d8 0x27)))
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108422 4 10 (.base 2 (.d8 0x27))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108422 0x44 (by decide) 2 (.base 2 (.d8 0x27)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (6, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083cc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (6, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083cf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (2, 2), (4, 4), (6, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083d4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 57), (2, 2), (4, 4), (6, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083d8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 57), (2, 2), (4, 4), (6, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083e0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 62), (2, 2), (4, 4), (6, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083e3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 62), (2, 2), (4, 4), (6, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083ea) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 65), (2, 2), (4, 4), (6, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083ef) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083f2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083f6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083fb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083ff) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108404) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108408) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10840e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108412) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 80), (9, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108418) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 80), (9, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10841c) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f18 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 80), (9, 84), (10, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108422) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f19 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 55), (1, 67), (2, 2), (4, 4), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108426) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1083c7_1 code

theorem block_l1083c7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1083c7 :=
  Rest.liftedBlock (rest_l1083c7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1083c7 x hx)

theorem rest_l1084c1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1084c1 bytes_l1084c1) (entryMap (live .l1084c1))
      8 0x1084c1 bytes_l1084c1 b_l1084c1 := by
  have f0 : InstrSpec 0x1084c1 [0x48, 0x81, 0xC4, 0xD8, 0x06, 0x00, 0x00] (fun s => s.RIP = 0x1084c1) (addR64Imm32Effect 0x1084c1 4 0x6d8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x1084c1 4 0x6d8).toInstrSpec (add_r64_imm32_effect_step 0x1084c1 0x48 0xc4 0x6d8 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1084c8 [0x5B] (PopPre 0x1084c8) (popR64Effect 0x1084c8 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1084c8 1 3).toInstrSpec (pop_r64_effect_step 0x1084c8 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1084c9 [0x41, 0x5C] (PopPre 0x1084c9) (popR64Effect 0x1084c9 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1084c9 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1084c9 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1084cb [0x41, 0x5D] (PopPre 0x1084cb) (popR64Effect 0x1084cb 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1084cb 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1084cb 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1084cd [0x41, 0x5E] (PopPre 0x1084cd) (popR64Effect 0x1084cd 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1084cd 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1084cd 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1084cf [0x41, 0x5F] (PopPre 0x1084cf) (popR64Effect 0x1084cf 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1084cf 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1084cf 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1084d1 [0x5D] (PopPre 0x1084d1) (popR64Effect 0x1084d1 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1084d1 1 5).toInstrSpec (pop_r64_effect_step 0x1084d1 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1084d2 [0xC3] (RetPre 0x1084d2) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1084d2).toInstrSpec (ret_effect_step 0x1084d2) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084c8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084c9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084cb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084cd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084cf) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084d1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084d2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l1084c1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1084c1 :=
  Rest.liftedBlock (rest_l1084c1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1084c1 x hx)

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

theorem_by block_l107050_eval :
    program.runBlock (dialect code) ⟨.l107050, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107090_eval :
    program.runBlock (dialect code) ⟨.l107090, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1070dd_eval :
    program.runBlock (dialect code) ⟨.l1070dd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107100_eval :
    program.runBlock (dialect code) ⟨.l107100, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10714a_eval :
    program.runBlock (dialect code) ⟨.l10714a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107170_eval :
    program.runBlock (dialect code) ⟨.l107170, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107298_eval :
    program.runBlock (dialect code) ⟨.l107298, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107a08_eval :
    program.runBlock (dialect code) ⟨.l107a08, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107b12_eval :
    program.runBlock (dialect code) ⟨.l107b12, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107b80_eval :
    program.runBlock (dialect code) ⟨.l107b80, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107b9f_eval :
    program.runBlock (dialect code) ⟨.l107b9f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107ba7_eval :
    program.runBlock (dialect code) ⟨.l107ba7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107c41_eval :
    program.runBlock (dialect code) ⟨.l107c41, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107c50_eval :
    program.runBlock (dialect code) ⟨.l107c50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107e96_eval :
    program.runBlock (dialect code) ⟨.l107e96, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107e9e_eval :
    program.runBlock (dialect code) ⟨.l107e9e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107f13_eval :
    program.runBlock (dialect code) ⟨.l107f13, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10805f_eval :
    program.runBlock (dialect code) ⟨.l10805f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1080c0_eval :
    program.runBlock (dialect code) ⟨.l1080c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108110_eval :
    program.runBlock (dialect code) ⟨.l108110, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10814d_eval :
    program.runBlock (dialect code) ⟨.l10814d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108178_eval :
    program.runBlock (dialect code) ⟨.l108178, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108299_eval :
    program.runBlock (dialect code) ⟨.l108299, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1083c7_eval :
    program.runBlock (dialect code) ⟨.l1083c7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1084c1_eval :
    program.runBlock (dialect code) ⟨.l1084c1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
