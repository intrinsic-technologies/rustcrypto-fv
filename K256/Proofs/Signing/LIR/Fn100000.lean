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

theorem rest_l100000_2 [Bindings] (code : CodeMap) :
    Rest (n := 129) code lifted (codeRange 0x100000 bytes_l100000) [(0, 71), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 112), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (22, 22), (39, 39), (50, 50), (51, 51)]
      17 0x100094 bytes_l100000_2 b_l100000_2 := by
  have f40 : InstrSpec 0x100094 [0x4D, 0x85, 0xD2] (fun s => s.RIP = 0x100094) (testR64R64Effect 0x100094 10 10)
      [.gpr 10, .gpr 10] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x100094 10 10).toInstrSpec (test_r64_r64_effect_step 0x100094 0x4d 0xd2 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x100097 [0x45, 0x0F, 0x45, 0xCB] (fun s => s.RIP = 0x100097) (atFlags (condHolds 5) (cmovR32R32Effect 0x100097 4 9 11))
      [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 9, .rip] :=
    (cmovR32R32Effect_footprint 0x100097 4 9 11 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_rex_effect_step 0x100097 5 0x45 (by decide) 0xcb (by decide) c)) pre_rip
  have f42 : InstrSpec 0x10009b [0x48, 0x0F, 0xBD, 0x06] (LoadPre 0x10009b (fun s => AddrMode.addr (.base 6 .none) s (0x10009b + BitVec.ofNat 64 4)) 8) (bsrR64M64Effect 0x10009b 4 0 (.base 6 .none))
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (bsrR64M64Effect_footprint 0x10009b 4 0 (.base 6 .none)).toInstrSpec (bsr_r64_m64_effect_step 0x10009b 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f43 : InstrSpec 0x10009f [0x83, 0xF0, 0x3F] (fun s => s.RIP = 0x10009f) (xorR32Imm8Effect 0x10009f 3 0 0x3f)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x10009f 3 0 0x3f).toInstrSpec (xor_r32_imm8_effect_step 0x10009f 0xf0 0x3f (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x1000a2 [0x44, 0x88, 0x4C, 0x24, 0x0F] (StorePre 0x1000a2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1000a2 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1000a2 5 9 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1000a2 5 9 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1000a2 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x1000a7 [0x0F, 0xB6, 0x74, 0x24, 0x0F] (LoadPre 0x1000a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1000a7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1000a7 5 6 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x1000a7 5 6 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_effect_step 0x1000a7 6 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f46 : InstrSpec 0x1000ac [0xF7, 0xDE] (fun s => s.RIP = 0x1000ac) (negR32Effect 0x1000ac 2 6)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (negR32Effect_footprint 0x1000ac 2 6).toInstrSpec (neg_r32_effect_step 0x1000ac 0xde (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x1000ae [0x21, 0xC6] (fun s => s.RIP = 0x1000ae) (andR32R32Effect 0x1000ae 2 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (andR32R32Effect_footprint 0x1000ae 2 6 0).toInstrSpec (and_r32_r32_effect_step 0x1000ae 0xc6 (by decide)) pre_rip
  have f48 : InstrSpec 0x1000b0 [0x49, 0x01, 0xD0] (fun s => s.RIP = 0x1000b0) (addR64R64Effect 0x1000b0 8 2)
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1000b0 8 2).toInstrSpec (add_r64_r64_effect_step 0x1000b0 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x1000b3 [0x4D, 0x01, 0xF8] (fun s => s.RIP = 0x1000b3) (addR64R64Effect 0x1000b3 8 15)
      [.gpr 8, .gpr 15] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1000b3 8 15).toInstrSpec (add_r64_r64_effect_step 0x1000b3 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x1000b6 [0x49, 0x01, 0xF0] (fun s => s.RIP = 0x1000b6) (addR64R64Effect 0x1000b6 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1000b6 8 6).toInstrSpec (add_r64_r64_effect_step 0x1000b6 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x1000b9 [0xB8, 0x07, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1000b9) (movR32Imm32Effect 0x1000b9 5 0 0x107)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1000b9 5 0 0x107).toInstrSpec (mov_r32_imm32_effect_step 0x1000b9 0xb8 (by decide) 0x107) pre_rip
  have f52 : InstrSpec 0x1000be [0x4C, 0x29, 0xC0] (fun s => s.RIP = 0x1000be) (subR64R64Effect 0x1000be 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1000be 0 8).toInstrSpec (sub_r64_r64_effect_step 0x1000be 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x1000c1 [0x89, 0xC2] (fun s => s.RIP = 0x1000c1) (movR32R32Effect 0x1000c1 2 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x1000c1 2 2 0).toInstrSpec (mov_r32_r32_effect_step 0x1000c1 0xc2 (by decide)) pre_rip
  have f54 : InstrSpec 0x1000c3 [0xC1, 0xEA, 0x03] (fun s => s.RIP = 0x1000c3) (shrR32Effect 0x1000c3 3 2 3)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x1000c3 3 2 3).toInstrSpec (shr_r32_imm8_effect_step 0x1000c3 0xea 0x3 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x1000c6 [0x48, 0x39, 0xD1] (fun s => s.RIP = 0x1000c6) (cmpR64R64Effect 0x1000c6 1 2)
      [.gpr 1, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1000c6 1 2).toInstrSpec (cmp_r64_r64_effect_step 0x1000c6 0x48 0xd1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f40 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 112), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (19, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100097) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f41 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 131), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (19, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10009b) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f42 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 133), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 131), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10009f) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f43 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 135), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 131), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000a2) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.exec (n := 137) (ρ' := [(0, 135), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 131), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000a7) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f45 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 135), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 138), (7, 7), (8, 106), (9, 131), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000ac) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f46 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 135), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 140), (7, 7), (8, 106), (9, 131), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000ae) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f47 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 135), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 142), (7, 7), (8, 106), (9, 131), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000b0) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f48 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 135), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 142), (7, 7), (8, 144), (9, 131), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000b3) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f49 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 135), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 142), (7, 7), (8, 146), (9, 131), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000b6) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f50 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 135), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 142), (7, 7), (8, 148), (9, 131), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000b9) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f51 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 150), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 142), (7, 7), (8, 148), (9, 131), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000be) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f52 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 152), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 142), (7, 7), (8, 148), (9, 131), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000c1) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f53 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 152), (1, 1), (2, 154), (3, 120), (4, 65), (5, 5), (6, 142), (7, 7), (8, 148), (9, 131), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000c3) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f54 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 152), (1, 1), (2, 156), (3, 120), (4, 65), (5, 5), (6, 142), (7, 7), (8, 148), (9, 131), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000c6) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f55 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 152), (1, 1), (2, 156), (3, 120), (4, 65), (5, 5), (6, 142), (7, 7), (8, 148), (9, 131), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (16, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000c9) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 160) (jcc_rel32_effect_step 0x1000c9 2 0x93) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l100000_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x100000 bytes_l100000) [(0, 71), (1, 1), (2, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 77), (10, 87), (11, 89), (12, 67), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      37 0x100046 bytes_l100000_1 b_l100000_1 := by
  have f20 : InstrSpec 0x100046 [0x4D, 0x0F, 0xBD, 0xDA] (fun s => s.RIP = 0x100046) (bsrR64R64Effect 0x100046 4 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (bsrR64R64Effect_footprint 0x100046 4 11 10).toInstrSpec (bsr_r64_r64_effect_step 0x100046 0x4d (by decide) 0xda (by decide)) pre_rip
  have f21 : InstrSpec 0x10004a [0x41, 0x83, 0xF3, 0x3F] (fun s => s.RIP = 0x10004a) (xorR32Imm8Effect 0x10004a 4 11 0x3f)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x10004a 4 11 0x3f).toInstrSpec (xor_r32_imm8_rex_effect_step 0x10004a 0x41 0xf3 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10004e [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x10004e) (xorR32R32Effect 0x10004e 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10004e 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x10004e 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x100051 [0x4D, 0x85, 0xC0] (fun s => s.RIP = 0x100051) (testR64R64Effect 0x100051 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x100051 8 8).toInstrSpec (test_r64_r64_effect_step 0x100051 0x4d 0xc0 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x100054 [0x41, 0x0F, 0x94, 0xC1] (fun s => s.RIP = 0x100054) (atFlags (condHolds 4) (setccR8Effect 0x100054 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x100054 4 9 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x100054 4 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f25 : InstrSpec 0x100058 [0x0F, 0x94, 0x44, 0x24, 0x0F] (StorePre 0x100058 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x100058 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x100058 5 (.sib 4 none 0 (.d8 0xf))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x100058 5 (.sib 4 none 0 (.d8 0xf)) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x100058 4 0 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x10005d [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x0F] (LoadPre 0x10005d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x10005d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10005d 6 8 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x10005d 6 8 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10005d 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x100063 [0x41, 0xF7, 0xD8] (fun s => s.RIP = 0x100063) (negR32Effect 0x100063 3 8)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (negR32Effect_footprint 0x100063 3 8).toInstrSpec (neg_r32_rex_effect_step 0x100063 0x41 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x100066 [0x45, 0x21, 0xD8] (fun s => s.RIP = 0x100066) (andR32R32Effect 0x100066 3 8 11)
      [.gpr 8, .gpr 11] [] [.reg 8, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100066 3 8 11).toInstrSpec (and_r32_r32_rex_effect_step 0x100066 0x45 0xd8 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x100069 [0x45, 0x31, 0xDB] (fun s => s.RIP = 0x100069) (xorR32R32Effect 0x100069 3 11 11)
      [.gpr 11, .gpr 11] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100069 3 11 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x100069 0x45 0xdb (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10006c [0x4D, 0x85, 0xD2] (fun s => s.RIP = 0x10006c) (testR64R64Effect 0x10006c 10 10)
      [.gpr 10, .gpr 10] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x10006c 10 10).toInstrSpec (test_r64_r64_effect_step 0x10006c 0x4d 0xd2 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x10006f [0x45, 0x0F, 0x45, 0xCB] (fun s => s.RIP = 0x10006f) (atFlags (condHolds 5) (cmovR32R32Effect 0x10006f 4 9 11))
      [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 9, .rip] :=
    (cmovR32R32Effect_footprint 0x10006f 4 9 11 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_rex_effect_step 0x10006f 5 0x45 (by decide) 0xcb (by decide) c)) pre_rip
  have f32 : InstrSpec 0x100073 [0x4C, 0x8B, 0x56, 0x08] (LoadPre 0x100073 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x100073 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100073 10 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x100073 10 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x100073 0x4c (by decide) 2 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x100077 [0xBB, 0x7F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100077) (movR32Imm32Effect 0x100077 5 3 0x7f)
      [] [] [.reg 3, .rip] :=
    (movR32Imm32Effect_footprint 0x100077 5 3 0x7f).toInstrSpec (mov_r32_imm32_effect_step 0x100077 0xbb (by decide) 0x7f) pre_rip
  have f34 : InstrSpec 0x10007c [0x49, 0x0F, 0xBD, 0xDA] (fun s => s.RIP = 0x10007c) (bsrR64R64Effect 0x10007c 4 3 10)
      [.gpr 3, .gpr 10] [] [.reg 3, .flags, .rip] :=
    (bsrR64R64Effect_footprint 0x10007c 4 3 10).toInstrSpec (bsr_r64_r64_effect_step 0x10007c 0x49 (by decide) 0xda (by decide)) pre_rip
  have f35 : InstrSpec 0x100080 [0x83, 0xF3, 0x3F] (fun s => s.RIP = 0x100080) (xorR32Imm8Effect 0x100080 3 3 0x3f)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x100080 3 3 0x3f).toInstrSpec (xor_r32_imm8_effect_step 0x100080 0xf3 0x3f (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x100083 [0x44, 0x88, 0x4C, 0x24, 0x0F] (StorePre 0x100083 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x100083 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x100083 5 9 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x100083 5 9 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_rex_effect_step 0x100083 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x100088 [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x0F] (LoadPre 0x100088 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x100088 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x100088 6 15 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x100088 6 15 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x100088 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f38 : InstrSpec 0x10008e [0x41, 0xF7, 0xDF] (fun s => s.RIP = 0x10008e) (negR32Effect 0x10008e 3 15)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (negR32Effect_footprint 0x10008e 3 15).toInstrSpec (neg_r32_rex_effect_step 0x10008e 0x41 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x100091 [0x41, 0x21, 0xDF] (fun s => s.RIP = 0x100091) (andR32R32Effect 0x100091 3 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100091 3 15 3).toInstrSpec (and_r32_r32_rex_effect_step 0x100091 0x41 0xdf (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 77), (10, 87), (11, 91), (12, 67), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10004a) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 77), (10, 87), (11, 93), (12, 67), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10004e) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 95), (10, 87), (11, 93), (12, 67), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100051) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 95), (10, 87), (11, 93), (12, 67), (13, 13), (15, 15), (19, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100054) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 99), (10, 87), (11, 93), (12, 67), (13, 13), (15, 15), (19, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100058) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 99), (10, 87), (11, 93), (12, 67), (13, 13), (15, 15), (19, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10005d) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f26 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 102), (9, 99), (10, 87), (11, 93), (12, 67), (13, 13), (15, 15), (19, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100063) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f27 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 104), (9, 99), (10, 87), (11, 93), (12, 67), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100066) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f28 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 99), (10, 87), (11, 93), (12, 67), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100069) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f29 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 99), (10, 87), (11, 108), (12, 67), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10006c) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f30 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 99), (10, 87), (11, 108), (12, 67), (13, 13), (15, 15), (19, 110), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10006f) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f31 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 112), (10, 87), (11, 108), (12, 67), (13, 13), (15, 15), (19, 110), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100073) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f32 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 112), (10, 114), (11, 108), (12, 67), (13, 13), (15, 15), (19, 110), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100077) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f33 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 116), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 112), (10, 114), (11, 108), (12, 67), (13, 13), (15, 15), (19, 110), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10007c) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f34 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 118), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 112), (10, 114), (11, 108), (12, 67), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100080) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f35 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 112), (10, 114), (11, 108), (12, 67), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100083) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.exec (n := 122) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 112), (10, 114), (11, 108), (12, 67), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100088) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 112), (10, 114), (11, 108), (12, 67), (13, 13), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10008e) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f38 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 112), (10, 114), (11, 108), (12, 67), (13, 13), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100091) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f39 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 106), (9, 112), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100094) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100000_2 code

theorem rest_l100000 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100000 bytes_l100000) (entryMap (live .l100000))
      57 0x100000 bytes_l100000 b_l100000 := by
  have f0 : InstrSpec 0x100000 [0x55] (PushPre 0x100000 1) (pushR64Effect 0x100000 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100000 1 5).toInstrSpec (push_r64_effect_step 0x100000 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x100001 [0x41, 0x57] (PushPre 0x100001 2) (pushR64Effect 0x100001 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100001 2 15).toInstrSpec (push_r64_rex_effect_step 0x100001 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x100003 [0x41, 0x56] (PushPre 0x100003 2) (pushR64Effect 0x100003 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100003 2 14).toInstrSpec (push_r64_rex_effect_step 0x100003 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x100005 [0x41, 0x55] (PushPre 0x100005 2) (pushR64Effect 0x100005 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100005 2 13).toInstrSpec (push_r64_rex_effect_step 0x100005 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x100007 [0x41, 0x54] (PushPre 0x100007 2) (pushR64Effect 0x100007 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100007 2 12).toInstrSpec (push_r64_rex_effect_step 0x100007 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x100009 [0x53] (PushPre 0x100009 1) (pushR64Effect 0x100009 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100009 1 3).toInstrSpec (push_r64_effect_step 0x100009 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10000a [0x48, 0x83, 0xEC, 0x18] (fun s => s.RIP = 0x10000a) (subR64Imm8Effect 0x10000a 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10000a 4 0x18).toInstrSpec (sub_r64_imm8_effect_step 0x10000a 0x48 0xec 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10000e [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x10000e) (movR64R64Effect 0x10000e 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10000e 12 2).toInstrSpec (mov_r64_r64_effect_step 0x10000e 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100011 [0x4C, 0x8B, 0x46, 0x18] (LoadPre 0x100011 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x100011 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100011 8 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x100011 8 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x100011 0x4c (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x100015 [0xB8, 0x7F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100015) (movR32Imm32Effect 0x100015 5 0 0x7f)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x100015 5 0 0x7f).toInstrSpec (mov_r32_imm32_effect_step 0x100015 0xb8 (by decide) 0x7f) pre_rip
  have f10 : InstrSpec 0x10001a [0x41, 0xB9, 0x7F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10001a) (movR32Imm32Effect 0x10001a 6 9 0x7f)
      [] [] [.reg 9, .rip] :=
    (movR32Imm32Effect_footprint 0x10001a 6 9 0x7f).toInstrSpec (mov_r32_imm32_rex_effect_step 0x10001a 0x41 0xb9 (by decide) (by decide) 0x7f) pre_rip
  have f11 : InstrSpec 0x100020 [0x4D, 0x0F, 0xBD, 0xC8] (fun s => s.RIP = 0x100020) (bsrR64R64Effect 0x100020 4 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (bsrR64R64Effect_footprint 0x100020 4 9 8).toInstrSpec (bsr_r64_r64_effect_step 0x100020 0x4d (by decide) 0xc8 (by decide)) pre_rip
  have f12 : InstrSpec 0x100024 [0x41, 0x83, 0xF1, 0x3F] (fun s => s.RIP = 0x100024) (xorR32Imm8Effect 0x100024 4 9 0x3f)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x100024 4 9 0x3f).toInstrSpec (xor_r32_imm8_rex_effect_step 0x100024 0x41 0xf1 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x100028 [0xC6, 0x44, 0x24, 0x0F, 0x01] (StorePre 0x100028 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x100028 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x100028 (.sib 4 none 0 (.d8 0xf)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x100028 (.sib 4 none 0 (.d8 0xf)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x100028 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x10002d [0x4C, 0x8D, 0x74, 0x24, 0x0F] (fun s => s.RIP = 0x10002d) (leaR64Effect 0x10002d 14 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x10002d 14 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (lea_r64_effect_step 0x10002d 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x100032 [0x0F, 0xB6, 0x54, 0x24, 0x0F] (LoadPre 0x100032 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x100032 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100032 5 2 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x100032 5 2 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_effect_step 0x100032 2 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x100037 [0xF7, 0xDA] (fun s => s.RIP = 0x100037) (negR32Effect 0x100037 2 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR32Effect_footprint 0x100037 2 2).toInstrSpec (neg_r32_effect_step 0x100037 0xda (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x100039 [0x44, 0x21, 0xCA] (fun s => s.RIP = 0x100039) (andR32R32Effect 0x100039 3 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100039 3 2 9).toInstrSpec (and_r32_r32_rex_effect_step 0x100039 0x44 0xca (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10003c [0x4C, 0x8B, 0x56, 0x10] (LoadPre 0x10003c (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10003c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10003c 10 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x10003c 10 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10003c 0x4c (by decide) 2 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x100040 [0x41, 0xBB, 0x7F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100040) (movR32Imm32Effect 0x100040 6 11 0x7f)
      [] [] [.reg 11, .rip] :=
    (movR32Imm32Effect_footprint 0x100040 6 11 0x7f).toInstrSpec (mov_r32_imm32_rex_effect_step 0x100040 0x41 0xbb (by decide) (by decide) 0x7f) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100001) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100003) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100005) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100007) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100009) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10000a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10000e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100011) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100015) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10001a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 73), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100020) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 75), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100024) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 77), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100028) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 77), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10002d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 77), (12, 67), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100032) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 71), (1, 1), (2, 81), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 77), (12, 67), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100037) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 71), (1, 1), (2, 83), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 77), (12, 67), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100039) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 77), (12, 67), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10003c) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 77), (10, 87), (12, 67), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100040) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 71), (1, 1), (2, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 77), (10, 87), (11, 89), (12, 67), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100046) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100000_1 code

theorem block_l100000 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100000 :=
  Rest.liftedBlock (rest_l100000 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100000 x hx)

theorem rest_l1000cf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1000cf bytes_l1000cf) (entryMap (live .l1000cf))
      2 0x1000cf bytes_l1000cf b_l1000cf := by
  have f0 : InstrSpec 0x1000cf [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x1000cf) (testR64R64Effect 0x1000cf 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1000cf 2 2).toInstrSpec (test_r64_r64_effect_step 0x1000cf 0x48 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000d2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1000d2 4 0x7b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1000cf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1000cf :=
  Rest.liftedBlock (rest_l1000cf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1000cf x hx)

theorem rest_l1000d8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1000d8 bytes_l1000d8) (entryMap (live .l1000d8))
      10 0x1000d8 bytes_l1000d8 b_l1000d8 := by
  have f0 : InstrSpec 0x1000d8 [0x89, 0xC1] (fun s => s.RIP = 0x1000d8) (movR32R32Effect 0x1000d8 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1000d8 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1000d8 0xc1 (by decide)) pre_rip
  have f1 : InstrSpec 0x1000da [0xC1, 0xE9, 0x06] (fun s => s.RIP = 0x1000da) (shrR32Effect 0x1000da 3 1 6)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1000da 3 1 6).toInstrSpec (shr_r32_imm8_effect_step 0x1000da 0xe9 0x6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1000dd [0x83, 0xE0, 0x38] (fun s => s.RIP = 0x1000dd) (andR32Imm8Effect 0x1000dd 3 0 0x38)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1000dd 3 0 0x38).toInstrSpec (and_r32_imm8_effect_step 0x1000dd 0xe0 0x38 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1000e0 [0x48, 0x83, 0xF8, 0x01] (fun s => s.RIP = 0x1000e0) (cmpR64Imm8Effect 0x1000e0 0 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1000e0 0 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x1000e0 0x48 0xf8 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1000e4 [0x48, 0x83, 0xD9, 0xFF] (fun s => s.RIP = 0x1000e4) (atFlags StatusFlags.CF (sbbR64Imm8Effect 0x1000e4 1 0xff))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .flags, .rip] :=
    (sbbR64Imm8Effect_footprint 0x1000e4 1 0xff).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_imm8_effect_step 0x1000e4 0x48 0xd9 0xff c (by decide) (by decide) (by decide))) pre_rip
  have f5 : InstrSpec 0x1000e8 [0x48, 0x83, 0xF9, 0x04] (fun s => s.RIP = 0x1000e8) (cmpR64Imm8Effect 0x1000e8 1 0x4)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1000e8 1 0x4).toInstrSpec (cmp_r64_imm8_effect_step 0x1000e8 0x48 0xf9 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1000ec [0x41, 0xBF, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1000ec) (movR32Imm32Effect 0x1000ec 6 15 0x4)
      [] [] [.reg 15, .rip] :=
    (movR32Imm32Effect_footprint 0x1000ec 6 15 0x4).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1000ec 0x41 0xbf (by decide) (by decide) 0x4) pre_rip
  have f7 : InstrSpec 0x1000f2 [0x4C, 0x0F, 0x42, 0xF9] (fun s => s.RIP = 0x1000f2) (atFlags (condHolds 2) (cmovR64R64Effect 0x1000f2 4 15 1))
      [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .rip] :=
    (cmovR64R64Effect_footprint 0x1000f2 4 15 1 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x1000f2 2 0x4c (by decide) 0xf9 (by decide) c)) pre_rip
  have f8 : InstrSpec 0x1000f6 [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x1000f6) (testR64R64Effect 0x1000f6 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1000f6 1 1).toInstrSpec (test_r64_r64_effect_step 0x1000f6 0x48 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000da) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000dd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000e0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000e4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 61), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000e8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 61), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (16, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000ec) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 61), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 65), (16, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000f2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 61), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 67), (16, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000f6) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 57), (1, 61), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 67), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000f9) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 71) (jcc_rel8_effect_step 0x1000f9 4 0x58) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1000d8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1000d8 :=
  Rest.liftedBlock (rest_l1000d8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1000d8 x hx)

theorem rest_l1000fb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1000fb bytes_l1000fb) (entryMap (live .l1000fb))
      6 0x1000fb bytes_l1000fb b_l1000fb := by
  have f0 : InstrSpec 0x1000fb [0x49, 0x89, 0xFD] (fun s => s.RIP = 0x1000fb) (movR64R64Effect 0x1000fb 13 7)
      [.gpr 7] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1000fb 13 7).toInstrSpec (mov_r64_r64_effect_step 0x1000fb 0x49 0xfd (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1000fe [0x4D, 0x89, 0xE6] (fun s => s.RIP = 0x1000fe) (movR64R64Effect 0x1000fe 14 12)
      [.gpr 12] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1000fe 14 12).toInstrSpec (mov_r64_r64_effect_step 0x1000fe 0x4d 0xe6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100101 [0x45, 0x31, 0xE4] (fun s => s.RIP = 0x100101) (xorR32R32Effect 0x100101 3 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100101 3 12 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x100101 0x45 0xe4 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100104 [0x31, 0xED] (fun s => s.RIP = 0x100104) (xorR32R32Effect 0x100104 2 5 5)
      [.gpr 5, .gpr 5] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100104 2 5 5).toInstrSpec (xor_r32_r32_effect_step 0x100104 0xed (by decide)) pre_rip
  have f4 : InstrSpec 0x100106 [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x100106) (movR64R64Effect 0x100106 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x100106 3 2).toInstrSpec (mov_r64_r64_effect_step 0x100106 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x100109 [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100109) (fun _ => nopEffect 0x100109 7)
      [] [] [.rip] :=
    (nopEffect_footprint 0x100109 7).toInstrSpec (nop_m_effect_step 0x100109 [] (by decide) (by decide) (.base 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000fe) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100101) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 57), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100104) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (4, 4), (5, 59), (7, 7), (9, 9), (10, 10), (11, 11), (12, 57), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100106) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 61), (4, 4), (5, 59), (7, 7), (9, 9), (10, 10), (11, 11), (12, 57), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100109) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(2, 2), (3, 61), (4, 4), (5, 59), (7, 7), (9, 9), (10, 10), (11, 11), (12, 57), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100110) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 64) (by decide) rfl

theorem block_l1000fb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1000fb :=
  Rest.liftedBlock (rest_l1000fb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1000fb x hx)

theorem rest_l100110 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100110 bytes_l100110) (entryMap (live .l100110))
      15 0x100110 bytes_l100110 b_l100110 := by
  have f0 : InstrSpec 0x100110 [0x49, 0x8B, 0x44, 0xED, 0x00] (LoadPre 0x100110 (fun s => AddrMode.addr (.sib 13 (some 5) 3 (.d8 0x0)) s (0x100110 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100110 0 (.sib 13 (some 5) 3 (.d8 0x0)))
      [.gpr 13, .gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100110 0 (.sib 13 (some 5) 3 (.d8 0x0))).toInstrSpec (mov_r64_m64_effect_step 0x100110 0x49 (by decide) 0 (.sib 13 (some 5) 3 (.d8 0x0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100115 [0x48, 0x0F, 0xC8] (fun s => s.RIP = 0x100115) (bswapR64Effect 0x100115 3 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (bswapR64Effect_footprint 0x100115 3 0).toInstrSpec (bswap_r64_effect_step 0x100115 0x48 (by decide) 0xc8 (by decide)) pre_rip
  have f2 : InstrSpec 0x100118 [0x48, 0x83, 0xEB, 0x08] (fun s => s.RIP = 0x100118) (subR64Imm8Effect 0x100118 3 0x8)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x100118 3 0x8).toInstrSpec (sub_r64_imm8_effect_step 0x100118 0x48 0xeb 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10011c [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x10011c) (movR64R64Effect 0x10011c 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10011c 7 3).toInstrSpec (mov_r64_r64_effect_step 0x10011c 0x48 0xdf (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10011f [0x49, 0x0F, 0x42, 0xFC] (fun s => s.RIP = 0x10011f) (atFlags (condHolds 2) (cmovR64R64Effect 0x10011f 4 7 12))
      [.gpr 7, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 7, .rip] :=
    (cmovR64R64Effect_footprint 0x10011f 4 7 12 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10011f 2 0x49 (by decide) 0xfc (by decide) c)) pre_rip
  have f5 : InstrSpec 0x100123 [0x48, 0x29, 0xFA] (fun s => s.RIP = 0x100123) (subR64R64Effect 0x100123 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x100123 2 7).toInstrSpec (sub_r64_r64_effect_step 0x100123 0x48 0xfa (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100126 [0xB9, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100126) (movR32Imm32Effect 0x100126 5 1 0x8)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x100126 5 1 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x100126 0xb9 (by decide) 0x8) pre_rip
  have f7 : InstrSpec 0x10012b [0x48, 0x29, 0xD1] (fun s => s.RIP = 0x10012b) (subR64R64Effect 0x10012b 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10012b 1 2).toInstrSpec (sub_r64_r64_effect_step 0x10012b 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10012e [0x49, 0x0F, 0x42, 0xCC] (fun s => s.RIP = 0x10012e) (atFlags (condHolds 2) (cmovR64R64Effect 0x10012e 4 1 12))
      [.gpr 1, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .rip] :=
    (cmovR64R64Effect_footprint 0x10012e 4 1 12 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10012e 2 0x49 (by decide) 0xcc (by decide) c)) pre_rip
  have f9 : InstrSpec 0x100132 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x100132 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100132 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100132 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100132 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x100132 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x100137 [0x48, 0x8D, 0x34, 0x0C] (fun s => s.RIP = 0x100137) (leaR64Effect 0x100137 6 (.sib 4 (some 1) 0 .none))
      [.gpr 4, .gpr 1] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x100137 6 (.sib 4 (some 1) 0 .none)).toInstrSpec (lea_r64_effect_step 0x100137 0x48 (by decide) 6 (.sib 4 (some 1) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10013b [0x48, 0x83, 0xC6, 0x10] (fun s => s.RIP = 0x10013b) (addR64Imm8Effect 0x10013b 6 0x10)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10013b 6 0x10).toInstrSpec (add_r64_imm8_effect_step 0x10013b 0x48 0xc6 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10013f [0x4C, 0x01, 0xF7] (fun s => s.RIP = 0x10013f) (addR64R64Effect 0x10013f 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10013f 7 14).toInstrSpec (add_r64_r64_effect_step 0x10013f 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x100142 [0x48, 0xFF, 0xC5] (fun s => s.RIP = 0x100142) (incR64Effect 0x100142 5)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (incR64Effect_footprint 0x100142 5).toInstrSpec (inc_r64_effect_step 0x100142 0x48 0xc5 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x100145 [0xFF, 0x15, 0x85, 0x3C, 0x10, 0x00] (GoesTo (CallMemPre 0x100145 (.rip 0x103c85)) (callEffect (callMemPtr 0x100145 (.rip 0x103c85)) (0x100145 + BitVec.ofNat 64 (callMemLen (.rip 0x103c85)))) 0x12a820) (callEffect (callMemPtr 0x100145 (.rip 0x103c85)) (0x100145 + BitVec.ofNat 64 (callMemLen (.rip 0x103c85))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x100145 (.rip 0x103c85)).toInstrSpec (call_m64_effect_step 0x100145 (.rip 0x103c85) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100115) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100118) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (2, 2), (3, 57), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10011c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 55), (2, 2), (3, 57), (4, 4), (5, 5), (7, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10011f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (2, 2), (3, 57), (4, 4), (5, 5), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100123) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 55), (2, 64), (3, 57), (4, 4), (5, 5), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100126) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 66), (2, 64), (3, 57), (4, 4), (5, 5), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10012b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f7 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 68), (2, 64), (3, 57), (4, 4), (5, 5), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10012e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 71), (2, 64), (3, 57), (4, 4), (5, 5), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100132) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 55), (1, 71), (2, 64), (3, 57), (4, 4), (5, 5), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100137) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 55), (1, 71), (2, 64), (3, 57), (4, 4), (5, 5), (6, 74), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10013b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 55), (1, 71), (2, 64), (3, 57), (4, 4), (5, 5), (6, 76), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10013f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 55), (1, 71), (2, 64), (3, 57), (4, 4), (5, 5), (6, 76), (7, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100142) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f13 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 55), (1, 71), (2, 64), (3, 57), (4, 4), (5, 80), (6, 76), (7, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100145) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 55), (1, 71), (2, 64), (3, 57), (4, 82), (5, 80), (6, 76), (7, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f14 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 84) (by decide) (by decide) rfl rfl

theorem block_l100110 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100110 :=
  Rest.liftedBlock (rest_l100110 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100110 x hx)

theorem rest_l10014b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10014b bytes_l10014b) (entryMap (live .l10014b))
      3 0x10014b bytes_l10014b b_l10014b := by
  have f0 : InstrSpec 0x10014b [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x10014b) (movR64R64Effect 0x10014b 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10014b 2 3).toInstrSpec (mov_r64_r64_effect_step 0x10014b 0x48 0xda (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10014e [0x49, 0x39, 0xEF] (fun s => s.RIP = 0x10014e) (cmpR64R64Effect 0x10014e 15 5)
      [.gpr 15, .gpr 5] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x10014e 15 5).toInstrSpec (cmp_r64_r64_effect_step 0x10014e 0x49 0xef (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10014e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100151) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x100151 5 0xbd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10014b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10014b :=
  Rest.liftedBlock (rest_l10014b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10014b x hx)

theorem rest_l100153 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100153 bytes_l100153) (entryMap (live .l100153))
      8 0x100153 bytes_l100153 b_l100153 := by
  have f0 : InstrSpec 0x100153 [0x48, 0x83, 0xC4, 0x18] (fun s => s.RIP = 0x100153) (addR64Imm8Effect 0x100153 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x100153 4 0x18).toInstrSpec (add_r64_imm8_effect_step 0x100153 0x48 0xc4 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100157 [0x5B] (PopPre 0x100157) (popR64Effect 0x100157 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100157 1 3).toInstrSpec (pop_r64_effect_step 0x100157 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x100158 [0x41, 0x5C] (PopPre 0x100158) (popR64Effect 0x100158 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100158 2 12).toInstrSpec (pop_r64_rex_effect_step 0x100158 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10015a [0x41, 0x5D] (PopPre 0x10015a) (popR64Effect 0x10015a 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10015a 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10015a 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10015c [0x41, 0x5E] (PopPre 0x10015c) (popR64Effect 0x10015c 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10015c 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10015c 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10015e [0x41, 0x5F] (PopPre 0x10015e) (popR64Effect 0x10015e 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10015e 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10015e 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x100160 [0x5D] (PopPre 0x100160) (popR64Effect 0x100160 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100160 1 5).toInstrSpec (pop_r64_effect_step 0x100160 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x100161 [0xC3] (RetPre 0x100161) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x100161).toInstrSpec (ret_effect_step 0x100161) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100157) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100158) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10015a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10015c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10015e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100160) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100161) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l100153 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100153 :=
  Rest.liftedBlock (rest_l100153 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100153 x hx)

theorem rest_l100162 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100162 bytes_l100162) (entryMap (live .l100162))
      5 0x100162 bytes_l100162 b_l100162 := by
  have f0 : InstrSpec 0x100162 [0x31, 0xFF] (fun s => s.RIP = 0x100162) (xorR32R32Effect 0x100162 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100162 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x100162 0xff (by decide)) pre_rip
  have f1 : InstrSpec 0x100164 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x100164) (movR64R64Effect 0x100164 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100164 6 2).toInstrSpec (mov_r64_r64_effect_step 0x100164 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100167 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x100167) (movR64R64Effect 0x100167 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x100167 2 1).toInstrSpec (mov_r64_r64_effect_step 0x100167 0x48 0xca (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10016a [0x48, 0xC7, 0xC1, 0x68, 0x20, 0x20, 0x00] (fun s => s.RIP = 0x10016a) (movR64Imm32Effect 0x10016a 1 0x202068)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x10016a 1 0x202068).toInstrSpec (mov_r64_imm32_effect_step 0x10016a 0x48 0xc1 (by decide) (by decide) (by decide) 0x202068) pre_rip
  have f4 : InstrSpec 0x100171 [0xE8, 0xEA, 0x99, 0x02, 0x00] (PushPre 0x100171 5) (callEffect (fun _ => 0x129b60) 0x100176)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100171 0x129b60 0x100176).toInstrSpec (call_rel32_effect_step 0x100171 0x299ea (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (7, 53)]) (p' := 0x100164) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100167) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10016a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 59), (2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100171) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 59), (2, 57), (4, 61), (5, 5), (6, 55), (7, 53)]) (p' := 0x129b60) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l100162 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100162 :=
  Rest.liftedBlock (rest_l100162 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100162 x hx)

theorem rest_l100176 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100176 bytes_l100176) (entryMap (live .l100176))
      1 0x100176 bytes_l100176 b_l100176 := by
  have f0 : InstrSpec 0x100176 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100176) (fun _ => nopEffect 0x100176 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x100176 10).toInstrSpec (nop_m_effect_step 0x100176 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100180) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l100176 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100176 :=
  Rest.liftedBlock (rest_l100176 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100176 x hx)

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

theorem_by block_l100000_eval :
    program.runBlock (dialect code) ⟨.l100000, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1000cf_eval :
    program.runBlock (dialect code) ⟨.l1000cf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1000d8_eval :
    program.runBlock (dialect code) ⟨.l1000d8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1000fb_eval :
    program.runBlock (dialect code) ⟨.l1000fb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100110_eval :
    program.runBlock (dialect code) ⟨.l100110, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10014b_eval :
    program.runBlock (dialect code) ⟨.l10014b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100153_eval :
    program.runBlock (dialect code) ⟨.l100153, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100162_eval :
    program.runBlock (dialect code) ⟨.l100162, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100176_eval :
    program.runBlock (dialect code) ⟨.l100176, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
