import K256.Proofs.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Eval
import X86Proofs.Instructions.Adc.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Adc.Generated.MImm32.Triple
import X86Proofs.Instructions.Adc.Generated.MImm8.Triple
import X86Proofs.Instructions.Adc.Generated.MR.Triple
import X86Proofs.Instructions.Add.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.MImm32.Triple
import X86Proofs.Instructions.Add.Generated.MImm8.Triple
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.And.Generated.M8Imm8.Triple
import X86Proofs.Instructions.And.Generated.MImm32.Triple
import X86Proofs.Instructions.And.Generated.MImm8.Triple
import X86Proofs.Instructions.And.Generated.MR.Triple
import X86Proofs.Instructions.Or.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Or.Generated.MImm32.Triple
import X86Proofs.Instructions.Or.Generated.MImm8.Triple
import X86Proofs.Instructions.Or.Generated.MR.Triple
import X86Proofs.Instructions.Sbb.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm32.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MR.Triple
import X86Proofs.Instructions.Setcc.Generated.M8.Triple
import X86Proofs.Instructions.Shld.Generated.MRCl.Triple
import X86Proofs.Instructions.Shld.Generated.MRImm8.Triple
import X86Proofs.Instructions.Shrd.Generated.MRCl.Triple
import X86Proofs.Instructions.Shrd.Generated.MRImm8.Triple
import X86Proofs.Instructions.Sub.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sub.Generated.MImm32.Triple
import X86Proofs.Instructions.Sub.Generated.MImm8.Triple
import X86Proofs.Instructions.Sub.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.MImm32.Triple
import X86Proofs.Instructions.Xor.Generated.MImm8.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

theorem rest_l100a20 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100a20 bytes_l100a20) (entryMap (live .l100a20))
      1 0x100a20 bytes_l100a20 b_l100a20 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x100a20 0xfe (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100a20 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100a20 :=
  Rest.liftedBlock (rest_l100a20 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100a20 x hx)

theorem rest_l102450 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102450 bytes_l102450) (entryMap (live .l102450))
      4 0x102450 bytes_l102450 b_l102450 := by
  have f0 : InstrSpec 0x102450 [0x53] (PushPre 0x102450 1) (pushR64Effect 0x102450 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102450 1 3).toInstrSpec (push_r64_effect_step 0x102450 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x102451 [0x48, 0x83, 0xEC, 0x50] (fun s => s.RIP = 0x102451) (subR64Imm8Effect 0x102451 4 0x50)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x102451 4 0x50).toInstrSpec (sub_r64_imm8_effect_step 0x102451 0x48 0xec 0x50 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102455 [0x48, 0x83, 0xFA, 0x40] (fun s => s.RIP = 0x102455) (cmpR64Imm8Effect 0x102455 2 0x40)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x102455 2 0x40).toInstrSpec (cmp_r64_imm8_effect_step 0x102455 0x48 0xfa 0x40 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102451) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102455) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102459) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x102459 5 0x7b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102450 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102450 :=
  Rest.liftedBlock (rest_l102450 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102450 x hx)

theorem rest_l10245b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10245b bytes_l10245b) (entryMap (live .l10245b))
      3 0x10245b bytes_l10245b b_l10245b := by
  have f0 : InstrSpec 0x10245b [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x10245b) (movR64R64Effect 0x10245b 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10245b 3 7).toInstrSpec (mov_r64_r64_effect_step 0x10245b 0x48 0xfb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10245e [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x10245e) (leaR64Effect 0x10245e 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10245e 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10245e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102463 [0xE8, 0x58, 0x16, 0x00, 0x00] (PushPre 0x102463 5) (callEffect (fun _ => 0x103ac0) 0x102468)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102463 0x103ac0 0x102468).toInstrSpec (call_rel32_effect_step 0x102463 0x1658 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10245e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102463) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 53), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ac0) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l10245b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10245b :=
  Rest.liftedBlock (rest_l10245b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10245b x hx)

theorem rest_l102468 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102468 bytes_l102468) (entryMap (live .l102468))
      2 0x102468 bytes_l102468 b_l102468 := by
  have f0 : InstrSpec 0x102468 [0x83, 0x7C, 0x24, 0x08, 0x01] (LoadPre 0x102468 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x102468 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x102468 5 32 (.sib 4 none 0 (.d8 0x8)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x102468 5 (.sib 4 none 0 (.d8 0x8)) 0x1).toInstrSpec (cmp_m32_imm8_effect_step 0x102468 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10246d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x10246d 4 0x70) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102468 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102468 :=
  Rest.liftedBlock (rest_l102468 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102468 x hx)

theorem rest_l10246f_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x10246f bytes_l10246f) [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      5 0x1024be bytes_l10246f_1 b_l10246f_1 := by
  have f20 : InstrSpec 0x1024be [0x48, 0x89, 0x7B, 0x20] (StorePre 0x1024be 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1024be + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1024be 7 (.base 3 (.d8 0x20)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1024be 7 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1024be 0x48 (by decide) 7 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x1024c2 [0x4C, 0x89, 0x43, 0x28] (StorePre 0x1024c2 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1024c2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1024c2 8 (.base 3 (.d8 0x28)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1024c2 8 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1024c2 0x4c (by decide) 0 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x1024c6 [0x4C, 0x89, 0x4B, 0x30] (StorePre 0x1024c6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x1024c6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1024c6 9 (.base 3 (.d8 0x30)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1024c6 9 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1024c6 0x4c (by decide) 1 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x1024ca [0x4C, 0x89, 0x53, 0x38] (StorePre 0x1024ca 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x1024ca + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1024ca 10 (.base 3 (.d8 0x38)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1024ca 10 (.base 3 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x1024ca 0x4c (by decide) 2 (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x1024ce [0x31, 0xC0] (fun s => s.RIP = 0x1024ce) (xorR32R32Effect 0x1024ce 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1024ce 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x1024ce 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024c2) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024c6) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024ca) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024ce) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 93), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024d0) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 95) (by decide) rfl

theorem rest_l10246f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10246f bytes_l10246f) (entryMap (live .l10246f))
      25 0x10246f bytes_l10246f b_l10246f := by
  have f0 : InstrSpec 0x10246f [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x10246f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10246f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10246f 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10246f 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10246f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x102474 [0x48, 0x0F, 0xC8] (fun s => s.RIP = 0x102474) (bswapR64Effect 0x102474 3 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (bswapR64Effect_footprint 0x102474 3 0).toInstrSpec (bswap_r64_effect_step 0x102474 0x48 (by decide) 0xc8 (by decide)) pre_rip
  have f2 : InstrSpec 0x102477 [0x48, 0x8B, 0x4C, 0x24, 0x20] (LoadPre 0x102477 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x102477 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102477 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x102477 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x102477 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10247c [0x48, 0x0F, 0xC9] (fun s => s.RIP = 0x10247c) (bswapR64Effect 0x10247c 3 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR64Effect_footprint 0x10247c 3 1).toInstrSpec (bswap_r64_effect_step 0x10247c 0x48 (by decide) 0xc9 (by decide)) pre_rip
  have f4 : InstrSpec 0x10247f [0x48, 0x8B, 0x54, 0x24, 0x10] (LoadPre 0x10247f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10247f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10247f 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10247f 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10247f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x102484 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x102484 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102484 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102484 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x102484 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x102484 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x102489 [0x48, 0x0F, 0xCE] (fun s => s.RIP = 0x102489) (bswapR64Effect 0x102489 3 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (bswapR64Effect_footprint 0x102489 3 6).toInstrSpec (bswap_r64_effect_step 0x102489 0x48 (by decide) 0xce (by decide)) pre_rip
  have f7 : InstrSpec 0x10248c [0x48, 0x0F, 0xCA] (fun s => s.RIP = 0x10248c) (bswapR64Effect 0x10248c 3 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR64Effect_footprint 0x10248c 3 2).toInstrSpec (bswap_r64_effect_step 0x10248c 0x48 (by decide) 0xca (by decide)) pre_rip
  have f8 : InstrSpec 0x10248f [0x48, 0x8B, 0x7C, 0x24, 0x48] (LoadPre 0x10248f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10248f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10248f 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10248f 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10248f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x102494 [0x48, 0x0F, 0xCF] (fun s => s.RIP = 0x102494) (bswapR64Effect 0x102494 3 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (bswapR64Effect_footprint 0x102494 3 7).toInstrSpec (bswap_r64_effect_step 0x102494 0x48 (by decide) 0xcf (by decide)) pre_rip
  have f10 : InstrSpec 0x102497 [0x4C, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x102497 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x102497 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102497 8 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x102497 8 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x102497 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10249c [0x49, 0x0F, 0xC8] (fun s => s.RIP = 0x10249c) (bswapR64Effect 0x10249c 3 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (bswapR64Effect_footprint 0x10249c 3 8).toInstrSpec (bswap_r64_effect_step 0x10249c 0x49 (by decide) 0xc8 (by decide)) pre_rip
  have f12 : InstrSpec 0x10249f [0x4C, 0x8B, 0x4C, 0x24, 0x38] (LoadPre 0x10249f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10249f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10249f 9 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x10249f 9 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10249f 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1024a4 [0x49, 0x0F, 0xC9] (fun s => s.RIP = 0x1024a4) (bswapR64Effect 0x1024a4 3 9)
      [.gpr 9] [] [.reg 9, .rip] :=
    (bswapR64Effect_footprint 0x1024a4 3 9).toInstrSpec (bswap_r64_effect_step 0x1024a4 0x49 (by decide) 0xc9 (by decide)) pre_rip
  have f14 : InstrSpec 0x1024a7 [0x4C, 0x8B, 0x54, 0x24, 0x30] (LoadPre 0x1024a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1024a7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1024a7 10 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1024a7 10 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1024a7 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1024ac [0x49, 0x0F, 0xCA] (fun s => s.RIP = 0x1024ac) (bswapR64Effect 0x1024ac 3 10)
      [.gpr 10] [] [.reg 10, .rip] :=
    (bswapR64Effect_footprint 0x1024ac 3 10).toInstrSpec (bswap_r64_effect_step 0x1024ac 0x49 (by decide) 0xca (by decide)) pre_rip
  have f16 : InstrSpec 0x1024af [0x48, 0x89, 0x03] (StorePre 0x1024af 3 (fun s => AddrMode.addr (.base 3 .none) s (0x1024af + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1024af 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1024af 0 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1024af 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x1024b2 [0x48, 0x89, 0x4B, 0x08] (StorePre 0x1024b2 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1024b2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1024b2 1 (.base 3 (.d8 0x8)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1024b2 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1024b2 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1024b6 [0x48, 0x89, 0x73, 0x10] (StorePre 0x1024b6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1024b6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1024b6 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1024b6 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1024b6 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1024ba [0x48, 0x89, 0x53, 0x18] (StorePre 0x1024ba 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1024ba + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1024ba 2 (.base 3 (.d8 0x18)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1024ba 2 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1024ba 0x48 (by decide) 2 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102474) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102477) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10247c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 59), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10247f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102484) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102489) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 65), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10248c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10248f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102494) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102497) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 73), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10249c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10249f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 77), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024a4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024a7) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024ac) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024af) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024b2) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024b6) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024ba) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024be) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10246f_1 code

theorem block_l10246f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10246f :=
  Rest.liftedBlock (rest_l10246f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10246f x hx)

theorem rest_l1024d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1024d0 bytes_l1024d0) (entryMap (live .l1024d0))
      3 0x1024d0 bytes_l1024d0 b_l1024d0 := by
  have f0 : InstrSpec 0x1024d0 [0x48, 0x83, 0xC4, 0x50] (fun s => s.RIP = 0x1024d0) (addR64Imm8Effect 0x1024d0 4 0x50)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1024d0 4 0x50).toInstrSpec (add_r64_imm8_effect_step 0x1024d0 0x48 0xc4 0x50 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1024d4 [0x5B] (PopPre 0x1024d4) (popR64Effect 0x1024d4 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1024d4 1 3).toInstrSpec (pop_r64_effect_step 0x1024d4 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1024d5 [0xC3] (RetPre 0x1024d5) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1024d5).toInstrSpec (ret_effect_step 0x1024d5) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024d4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024d5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f2 (by decide) rfl rfl rfl (by decide)

theorem block_l1024d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1024d0 :=
  Rest.liftedBlock (rest_l1024d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1024d0 x hx)

theorem rest_l1024d6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1024d6 bytes_l1024d6) (entryMap (live .l1024d6))
      1 0x1024d6 bytes_l1024d6 b_l1024d6 := by
  have f0 : InstrSpec 0x1024d6 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1024d6 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1024d6 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1024d6 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1024d6 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1024d6 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024df) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l1024d6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1024d6 :=
  Rest.liftedBlock (rest_l1024d6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1024d6 x hx)

theorem rest_l1024df [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1024df bytes_l1024df) (entryMap (live .l1024df))
      4 0x1024df bytes_l1024df b_l1024df := by
  have f0 : InstrSpec 0x1024df [0x48, 0x8B, 0x7C, 0x24, 0x10] (LoadPre 0x1024df (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1024df + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1024df 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1024df 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1024df 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1024e4 [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1024e4) (movR32Imm32Effect 0x1024e4 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1024e4 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1024e4 0xb8 (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x1024e9 [0x48, 0x85, 0xFF] (fun s => s.RIP = 0x1024e9) (testR64R64Effect 0x1024e9 7 7)
      [.gpr 7, .gpr 7] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1024e9 7 7).toInstrSpec (test_r64_r64_effect_step 0x1024e9 0x48 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024e4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024e9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024ec) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x1024ec 4 0xe2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1024df [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1024df :=
  Rest.liftedBlock (rest_l1024df code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1024df x hx)

theorem rest_l1024ee [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1024ee bytes_l1024ee) (entryMap (live .l1024ee))
      4 0x1024ee bytes_l1024ee b_l1024ee := by
  have f0 : InstrSpec 0x1024ee [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x1024ee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1024ee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1024ee 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1024ee 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1024ee 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1024f3 [0x48, 0x8B, 0x09] (LoadPre 0x1024f3 (fun s => AddrMode.addr (.base 1 .none) s (0x1024f3 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1024f3 1 (.base 1 .none))
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1024f3 1 (.base 1 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1024f3 0x48 (by decide) 1 (.base 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1024f6 [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x1024f6) (testR64R64Effect 0x1024f6 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1024f6 1 1).toInstrSpec (test_r64_r64_effect_step 0x1024f6 0x48 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024f3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024f6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1024f9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x1024f9 4 0xd5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1024ee [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1024ee :=
  Rest.liftedBlock (rest_l1024ee code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1024ee x hx)

theorem rest_l1024fb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1024fb bytes_l1024fb) (entryMap (live .l1024fb))
      0 0x1024fb bytes_l1024fb b_l1024fb := by
  exact Rest.cut

theorem block_l1024fb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1024fb :=
  Rest.liftedBlock (rest_l1024fb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1024fb x hx)

theorem rest_l1024fd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1024fd bytes_l1024fd) (entryMap (live .l1024fd))
      4 0x1024fd bytes_l1024fd b_l1024fd := by
  have f0 : InstrSpec 0x1024fd [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1024fd) (movR32Imm32Effect 0x1024fd 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1024fd 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1024fd 0xb8 (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x102502 [0x48, 0x83, 0xC4, 0x50] (fun s => s.RIP = 0x102502) (addR64Imm8Effect 0x102502 4 0x50)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x102502 4 0x50).toInstrSpec (add_r64_imm8_effect_step 0x102502 0x48 0xc4 0x50 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102506 [0x5B] (PopPre 0x102506) (popR64Effect 0x102506 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102506 1 3).toInstrSpec (pop_r64_effect_step 0x102506 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x102507 [0xC3] (RetPre 0x102507) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x102507).toInstrSpec (ret_effect_step 0x102507) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102502) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102506) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102507) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f3 (by decide) rfl rfl rfl (by decide)

theorem block_l1024fd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1024fd :=
  Rest.liftedBlock (rest_l1024fd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1024fd x hx)

theorem rest_l127d50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127d50 bytes_l127d50) (entryMap (live .l127d50))
      5 0x127d50 bytes_l127d50 b_l127d50 := by
  have f0 : InstrSpec 0x127d50 [0x48, 0x83, 0xEC, 0x01] (fun s => s.RIP = 0x127d50) (subR64Imm8Effect 0x127d50 4 0x1)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x127d50 4 0x1).toInstrSpec (sub_r64_imm8_effect_step 0x127d50 0x48 0xec 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127d54 [0x40, 0x88, 0x3C, 0x24] (StorePre 0x127d54 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x127d54 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x127d54 4 7 (.sib 4 none 0 .none))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x127d54 4 7 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x127d54 0x40 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127d58 [0x0F, 0xB6, 0x04, 0x24] (LoadPre 0x127d58 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x127d58 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x127d58 4 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x127d58 4 0 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x127d58 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x127d5c [0x48, 0x83, 0xC4, 0x01] (fun s => s.RIP = 0x127d5c) (addR64Imm8Effect 0x127d5c 4 0x1)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x127d5c 4 0x1).toInstrSpec (add_r64_imm8_effect_step 0x127d5c 0x48 0xc4 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127d60 [0xC3] (RetPre 0x127d60) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127d60).toInstrSpec (ret_effect_step 0x127d60) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d54) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d58) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d5c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d60) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 62) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l127d50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127d50 :=
  Rest.liftedBlock (rest_l127d50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127d50 x hx)

theorem rest_l127f50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127f50 bytes_l127f50) (entryMap (live .l127f50))
      2 0x127f50 bytes_l127f50 b_l127f50 := by
  have f0 : InstrSpec 0x127f50 [0x48, 0x39, 0xCE] (fun s => s.RIP = 0x127f50) (cmpR64R64Effect 0x127f50 6 1)
      [.gpr 6, .gpr 1] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x127f50 6 1).toInstrSpec (cmp_r64_r64_effect_step 0x127f50 0x48 0xce (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f53) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x127f53 5 0x45) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127f50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127f50 :=
  Rest.liftedBlock (rest_l127f50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127f50 x hx)

theorem rest_l127f55 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127f55 bytes_l127f55) (entryMap (live .l127f55))
      2 0x127f55 bytes_l127f55 b_l127f55 := by
  have f0 : InstrSpec 0x127f55 [0x48, 0x85, 0xF6] (fun s => s.RIP = 0x127f55) (testR64R64Effect 0x127f55 6 6)
      [.gpr 6, .gpr 6] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x127f55 6 6).toInstrSpec (test_r64_r64_effect_step 0x127f55 0x48 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f58) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x127f58 4 0x4f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127f55 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127f55 :=
  Rest.liftedBlock (rest_l127f55 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127f55 x hx)

theorem rest_l127f5a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127f5a bytes_l127f5a) (entryMap (live .l127f5a))
      4 0x127f5a bytes_l127f5a b_l127f5a := by
  have f0 : InstrSpec 0x127f5a [0x66, 0xB8, 0x01, 0x00] (fun s => s.RIP = 0x127f5a) (movR16Imm16Effect 0x127f5a 4 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR16Imm16Effect_footprint 0x127f5a 4 0 0x1).toInstrSpec (mov_r16_imm16_effect_step 0x127f5a 0xb8 (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x127f5e [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x127f5e) (xorR32R32Effect 0x127f5e 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127f5e 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x127f5e 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127f61 [0x31, 0xC9] (fun s => s.RIP = 0x127f61) (xorR32R32Effect 0x127f61 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127f61 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x127f61 0xc9 (by decide)) pre_rip
  have f3 : InstrSpec 0x127f63 [0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127f63) (fun _ => nopEffect 0x127f63 13)
      [] [] [.rip] :=
    (nopEffect_footprint 0x127f63 13).toInstrSpec (nop_m_effect_step 0x127f63 [0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f5e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f61) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f63) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f70) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l127f5a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127f5a :=
  Rest.liftedBlock (rest_l127f5a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127f5a x hx)

theorem rest_l127f70 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127f70 bytes_l127f70) (entryMap (live .l127f70))
      8 0x127f70 bytes_l127f70 b_l127f70 := by
  have f0 : InstrSpec 0x127f70 [0x4E, 0x8B, 0x0C, 0xC7] (LoadPre 0x127f70 (fun s => AddrMode.addr (.sib 7 (some 8) 3 .none) s (0x127f70 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x127f70 9 (.sib 7 (some 8) 3 .none))
      [.gpr 7, .gpr 8] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x127f70 9 (.sib 7 (some 8) 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x127f70 0x4e (by decide) 1 (.sib 7 (some 8) 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127f74 [0x4E, 0x8B, 0x14, 0xC2] (LoadPre 0x127f74 (fun s => AddrMode.addr (.sib 2 (some 8) 3 .none) s (0x127f74 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x127f74 10 (.sib 2 (some 8) 3 .none))
      [.gpr 2, .gpr 8] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x127f74 10 (.sib 2 (some 8) 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x127f74 0x4e (by decide) 2 (.sib 2 (some 8) 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x127f78 [0x49, 0xFF, 0xC0] (fun s => s.RIP = 0x127f78) (incR64Effect 0x127f78 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (incR64Effect_footprint 0x127f78 8).toInstrSpec (inc_r64_effect_step 0x127f78 0x49 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x127f7b [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x127f7b) (movzxR32R8Effect 0x127f7b 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x127f7b 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x127f7b 0xc0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127f7e [0x4D, 0x31, 0xD1] (fun s => s.RIP = 0x127f7e) (xorR64R64Effect 0x127f7e 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x127f7e 9 10).toInstrSpec (xor_r64_r64_effect_step 0x127f7e 0x4d 0xd1 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x127f81 [0x48, 0x0F, 0x45, 0xC1] (fun s => s.RIP = 0x127f81) (atFlags (condHolds 5) (cmovR64R64Effect 0x127f81 4 0 1))
      [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (cmovR64R64Effect_footprint 0x127f81 4 0 1 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x127f81 5 0x48 (by decide) 0xc1 (by decide) c)) pre_rip
  have f6 : InstrSpec 0x127f85 [0x4C, 0x39, 0xC6] (fun s => s.RIP = 0x127f85) (cmpR64R64Effect 0x127f85 6 8)
      [.gpr 6, .gpr 8] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x127f85 6 8).toInstrSpec (cmp_r64_r64_effect_step 0x127f85 0x4c 0xc6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f74) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f78) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 53), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f7b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 53), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f7e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 61), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f81) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 61), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f85) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 61), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f88) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 68) (jcc_rel8_effect_step 0x127f88 5 0xe6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127f70 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127f70 :=
  Rest.liftedBlock (rest_l127f70 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127f70 x hx)

theorem rest_l127f8a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127f8a bytes_l127f8a) (entryMap (live .l127f8a))
      6 0x127f8a bytes_l127f8a b_l127f8a := by
  have f0 : InstrSpec 0x127f8a [0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x127f8a) (movzxR32R8Effect 0x127f8a 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x127f8a 3 1 0).toInstrSpec (movzx_r32_r8_effect_step 0x127f8a 0xc8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127f8d [0x31, 0xC0] (fun s => s.RIP = 0x127f8d) (xorR32R32Effect 0x127f8d 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127f8d 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x127f8d 0xc0 (by decide)) pre_rip
  have f2 : InstrSpec 0x127f8f [0x66, 0xBA, 0x01, 0x00] (fun s => s.RIP = 0x127f8f) (movR16Imm16Effect 0x127f8f 4 2 0x1)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR16Imm16Effect_footprint 0x127f8f 4 2 0x1).toInstrSpec (mov_r16_imm16_effect_step 0x127f8f 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x127f93 [0x66, 0x31, 0xD1] (fun s => s.RIP = 0x127f93) (xorR16R16Effect 0x127f93 3 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR16R16Effect_footprint 0x127f93 3 1 2).toInstrSpec (xor_r16_r16_effect_step 0x127f93 0xd1 (by decide)) pre_rip
  have f4 : InstrSpec 0x127f96 [0x0F, 0x44, 0xC2] (fun s => s.RIP = 0x127f96) (atFlags (condHolds 4) (cmovR32R32Effect 0x127f96 3 0 2))
      [.gpr 0, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (cmovR32R32Effect_footprint 0x127f96 3 0 2 4).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_effect_step 0x127f96 4 0xc2 (by decide) c)) pre_rip
  have f5 : InstrSpec 0x127f99 [0xC3] (RetPre 0x127f99) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127f99).toInstrSpec (ret_effect_step 0x127f99) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f8d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f8f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f93) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f96) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f99) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 66) (ρ' := [(0, 62), (1, 59), (2, 57), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l127f8a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127f8a :=
  Rest.liftedBlock (rest_l127f8a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127f8a x hx)

theorem rest_l127f9a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127f9a bytes_l127f9a) (entryMap (live .l127f9a))
      6 0x127f9a bytes_l127f9a b_l127f9a := by
  have f0 : InstrSpec 0x127f9a [0x31, 0xC9] (fun s => s.RIP = 0x127f9a) (xorR32R32Effect 0x127f9a 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127f9a 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x127f9a 0xc9 (by decide)) pre_rip
  have f1 : InstrSpec 0x127f9c [0x31, 0xC0] (fun s => s.RIP = 0x127f9c) (xorR32R32Effect 0x127f9c 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127f9c 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x127f9c 0xc0 (by decide)) pre_rip
  have f2 : InstrSpec 0x127f9e [0x66, 0xBA, 0x01, 0x00] (fun s => s.RIP = 0x127f9e) (movR16Imm16Effect 0x127f9e 4 2 0x1)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR16Imm16Effect_footprint 0x127f9e 4 2 0x1).toInstrSpec (mov_r16_imm16_effect_step 0x127f9e 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x127fa2 [0x66, 0x31, 0xD1] (fun s => s.RIP = 0x127fa2) (xorR16R16Effect 0x127fa2 3 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR16R16Effect_footprint 0x127fa2 3 1 2).toInstrSpec (xor_r16_r16_effect_step 0x127fa2 0xd1 (by decide)) pre_rip
  have f4 : InstrSpec 0x127fa5 [0x0F, 0x44, 0xC2] (fun s => s.RIP = 0x127fa5) (atFlags (condHolds 4) (cmovR32R32Effect 0x127fa5 3 0 2))
      [.gpr 0, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (cmovR32R32Effect_footprint 0x127fa5 3 0 2 4).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_effect_step 0x127fa5 4 0xc2 (by decide) c)) pre_rip
  have f5 : InstrSpec 0x127fa8 [0xC3] (RetPre 0x127fa8) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127fa8).toInstrSpec (ret_effect_step 0x127fa8) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f9c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f9e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fa2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fa5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fa8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 66) (ρ' := [(0, 62), (1, 59), (2, 57), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l127f9a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127f9a :=
  Rest.liftedBlock (rest_l127f9a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127f9a x hx)

theorem rest_l127fa9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127fa9 bytes_l127fa9) (entryMap (live .l127fa9))
      6 0x127fa9 bytes_l127fa9 b_l127fa9 := by
  have f0 : InstrSpec 0x127fa9 [0x66, 0xB9, 0x01, 0x00] (fun s => s.RIP = 0x127fa9) (movR16Imm16Effect 0x127fa9 4 1 0x1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR16Imm16Effect_footprint 0x127fa9 4 1 0x1).toInstrSpec (mov_r16_imm16_effect_step 0x127fa9 0xb9 (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x127fad [0x31, 0xC0] (fun s => s.RIP = 0x127fad) (xorR32R32Effect 0x127fad 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127fad 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x127fad 0xc0 (by decide)) pre_rip
  have f2 : InstrSpec 0x127faf [0x66, 0xBA, 0x01, 0x00] (fun s => s.RIP = 0x127faf) (movR16Imm16Effect 0x127faf 4 2 0x1)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR16Imm16Effect_footprint 0x127faf 4 2 0x1).toInstrSpec (mov_r16_imm16_effect_step 0x127faf 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x127fb3 [0x66, 0x31, 0xD1] (fun s => s.RIP = 0x127fb3) (xorR16R16Effect 0x127fb3 3 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR16R16Effect_footprint 0x127fb3 3 1 2).toInstrSpec (xor_r16_r16_effect_step 0x127fb3 0xd1 (by decide)) pre_rip
  have f4 : InstrSpec 0x127fb6 [0x0F, 0x44, 0xC2] (fun s => s.RIP = 0x127fb6) (atFlags (condHolds 4) (cmovR32R32Effect 0x127fb6 3 0 2))
      [.gpr 0, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (cmovR32R32Effect_footprint 0x127fb6 3 0 2 4).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_effect_step 0x127fb6 4 0xc2 (by decide) c)) pre_rip
  have f5 : InstrSpec 0x127fb9 [0xC3] (RetPre 0x127fb9) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127fb9).toInstrSpec (ret_effect_step 0x127fb9) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fad) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127faf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fb3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fb6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fb9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 66) (ρ' := [(0, 62), (1, 59), (2, 57), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l127fa9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127fa9 :=
  Rest.liftedBlock (rest_l127fa9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127fa9 x hx)

theorem rest_l1295f2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1295f2 bytes_l1295f2) (entryMap (live .l1295f2))
      15 0x1295f2 bytes_l1295f2 b_l1295f2 := by
  have f0 : InstrSpec 0x1295f2 [0x55] (PushPre 0x1295f2 1) (pushR64Effect 0x1295f2 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1295f2 1 5).toInstrSpec (push_r64_effect_step 0x1295f2 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1295f3 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x1295f3) (movR64R64Effect 0x1295f3 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x1295f3 5 4).toInstrSpec (mov_r64_r64_effect_step 0x1295f3 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1295f6 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x1295f6) (subR64Imm8Effect 0x1295f6 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1295f6 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x1295f6 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1295fa [0x48, 0x8D, 0x45, 0xF8] (fun s => s.RIP = 0x1295fa) (leaR64Effect 0x1295fa 0 (.base 5 (.d8 0xf8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1295fa 0 (.base 5 (.d8 0xf8))).toInstrSpec (lea_r64_effect_step 0x1295fa 0x48 (by decide) 0 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1295fe [0x48, 0x89, 0x38] (StorePre 0x1295fe 3 (fun s => AddrMode.addr (.base 0 .none) s (0x1295fe + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1295fe 7 (.base 0 .none))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x1295fe 7 (.base 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1295fe 0x48 (by decide) 7 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x129601 [0x48, 0x8D, 0x4D, 0xF0] (fun s => s.RIP = 0x129601) (leaR64Effect 0x129601 1 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x129601 1 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x129601 0x48 (by decide) 1 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129605 [0x48, 0x89, 0x31] (StorePre 0x129605 3 (fun s => AddrMode.addr (.base 1 .none) s (0x129605 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x129605 6 (.base 1 .none))
      [.gpr 6, .gpr 1] [] [.rip] :=
    (movM64R64Effect_footprint 0x129605 6 (.base 1 .none)).toInstrSpec (mov_m64_r64_effect_step 0x129605 0x48 (by decide) 6 (.base 1 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x129608 [0x48, 0x8D, 0x75, 0xD0] (fun s => s.RIP = 0x129608) (leaR64Effect 0x129608 6 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x129608 6 (.base 5 (.d8 0xd0))).toInstrSpec (lea_r64_effect_step 0x129608 0x48 (by decide) 6 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12960c [0x48, 0x89, 0x0E] (StorePre 0x12960c 3 (fun s => AddrMode.addr (.base 6 .none) s (0x12960c + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x12960c 1 (.base 6 .none))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x12960c 1 (.base 6 .none)).toInstrSpec (mov_m64_r64_effect_step 0x12960c 0x48 (by decide) 1 (.base 6 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12960f [0x48, 0x8D, 0x0D, 0x1A, 0x0E, 0x00, 0x00] (fun s => s.RIP = 0x12960f) (leaR64Effect 0x12960f 1 (.rip 0xe1a))
      [] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x12960f 1 (.rip 0xe1a)).toInstrSpec (lea_r64_effect_step 0x12960f 0x48 (by decide) 1 (.rip 0xe1a) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129616 [0x48, 0x89, 0x4E, 0x08] (StorePre 0x129616 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x129616 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129616 1 (.base 6 (.d8 0x8)))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x129616 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x129616 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x12961a [0x48, 0x89, 0x46, 0x10] (StorePre 0x12961a 4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x12961a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12961a 0 (.base 6 (.d8 0x10)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x12961a 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x12961a 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x12961e [0x48, 0x89, 0x4E, 0x18] (StorePre 0x12961e 4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x12961e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12961e 1 (.base 6 (.d8 0x18)))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x12961e 1 (.base 6 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x12961e 0x48 (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x129622 [0x48, 0x8D, 0x3D, 0x32, 0x84, 0x0D, 0x00] (fun s => s.RIP = 0x129622) (leaR64Effect 0x129622 7 (.rip 0xd8432))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x129622 7 (.rip 0xd8432)).toInstrSpec (lea_r64_effect_step 0x129622 0x48 (by decide) 7 (.rip 0xd8432) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x129629 [0xFF, 0x15, 0xB1, 0xA7, 0x0D, 0x00] (GoesTo (CallMemPre 0x129629 (.rip 0xda7b1)) (callEffect (callMemPtr 0x129629 (.rip 0xda7b1)) (0x129629 + BitVec.ofNat 64 (callMemLen (.rip 0xda7b1)))) 0x129770) (callEffect (callMemPtr 0x129629 (.rip 0xda7b1)) (0x129629 + BitVec.ofNat 64 (callMemLen (.rip 0xda7b1))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x129629 (.rip 0xda7b1)).toInstrSpec (call_m64_effect_step 0x129629 (.rip 0xda7b1) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 53), (5, 5), (6, 6), (7, 7)]) (p' := 0x1295f3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 53), (5, 55), (6, 6), (7, 7)]) (p' := 0x1295f6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x1295fa) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x1295fe) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129601) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 62), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129605) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 62), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129608) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 62), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x12960c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 59), (1, 62), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x12960f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x129616) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x12961a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x12961e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x129622) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 57), (5, 55), (6, 65), (7, 73)]) (p' := 0x129629) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 75), (5, 55), (6, 65), (7, 73)]) (p' := 0x129770) f14 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l1295f2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1295f2 :=
  Rest.liftedBlock (rest_l1295f2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1295f2 x hx)

theorem rest_l12962f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12962f bytes_l12962f) (entryMap (live .l12962f))
      13 0x12962f bytes_l12962f b_l12962f := by
  have f0 : InstrSpec 0x12962f [0x90] (fun s => s.RIP = 0x12962f) (fun _ => nopEffect 0x12962f 1)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12962f 1).toInstrSpec (nop_effect_step 0x12962f) pre_rip
  have f1 : InstrSpec 0x129630 [0x55] (PushPre 0x129630 1) (pushR64Effect 0x129630 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129630 1 5).toInstrSpec (push_r64_effect_step 0x129630 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x129631 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129631) (movR64R64Effect 0x129631 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129631 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129631 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129634 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x129634) (subR64Imm8Effect 0x129634 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x129634 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x129634 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129638 [0x48, 0x89, 0x7D, 0xD8] (StorePre 0x129638 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x129638 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129638 7 (.base 5 (.d8 0xd8)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129638 7 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x129638 0x48 (by decide) 7 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12963c [0x48, 0x89, 0x75, 0xE0] (StorePre 0x12963c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x12963c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12963c 6 (.base 5 (.d8 0xe0)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12963c 6 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x12963c 0x48 (by decide) 6 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x129640 [0x48, 0x8D, 0x45, 0xD8] (fun s => s.RIP = 0x129640) (leaR64Effect 0x129640 0 (.base 5 (.d8 0xd8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129640 0 (.base 5 (.d8 0xd8))).toInstrSpec (lea_r64_effect_step 0x129640 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x129644 [0x48, 0x89, 0x45, 0xE8] (StorePre 0x129644 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x129644 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129644 0 (.base 5 (.d8 0xe8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129644 0 (.base 5 (.d8 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x129644 0x48 (by decide) 0 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x129648 [0x48, 0x89, 0x4D, 0xF0] (StorePre 0x129648 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x129648 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129648 1 (.base 5 (.d8 0xf0)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129648 1 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x129648 0x48 (by decide) 1 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12964c [0xC6, 0x45, 0xF8, 0x00] (StorePre 0x12964c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x12964c + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x12964c (.base 5 (.d8 0xf8)) 0x0)
      [.gpr 5] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x12964c (.base 5 (.d8 0xf8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x12964c (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x129650 [0x88, 0x55, 0xF9] (StorePre 0x129650 3 (fun s => AddrMode.addr (.base 5 (.d8 0xf9)) s (0x129650 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x129650 3 2 (.base 5 (.d8 0xf9)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x129650 3 2 (.base 5 (.d8 0xf9))).toInstrSpec (mov_m8_r8_effect_step 0x129650 2 (by decide) (.base 5 (.d8 0xf9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x129653 [0x48, 0x8D, 0x7D, 0xE8] (fun s => s.RIP = 0x129653) (leaR64Effect 0x129653 7 (.base 5 (.d8 0xe8)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x129653 7 (.base 5 (.d8 0xe8))).toInstrSpec (lea_r64_effect_step 0x129653 0x48 (by decide) 7 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x129657 [0xFF, 0x15, 0xC3, 0xA7, 0x0D, 0x00] (GoesTo (CallMemPre 0x129657 (.rip 0xda7c3)) (callEffect (callMemPtr 0x129657 (.rip 0xda7c3)) (0x129657 + BitVec.ofNat 64 (callMemLen (.rip 0xda7c3)))) 0x100a20) (callEffect (callMemPtr 0x129657 (.rip 0xda7c3)) (0x129657 + BitVec.ofNat 64 (callMemLen (.rip 0xda7c3))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x129657 (.rip 0xda7c3)).toInstrSpec (call_m64_effect_step 0x129657 (.rip 0xda7c3) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x100a20
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x129630) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (4, 54), (5, 5), (6, 6), (7, 7)]) (p' := 0x129631) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 1), (2, 2), (4, 54), (5, 56), (6, 6), (7, 7)]) (p' := 0x129634) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 1), (2, 2), (4, 58), (5, 56), (6, 6), (7, 7)]) (p' := 0x129638) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (4, 58), (5, 56), (6, 6), (7, 7)]) (p' := 0x12963c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(1, 1), (2, 2), (4, 58), (5, 56), (6, 6), (7, 7)]) (p' := 0x129640) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 1), (2, 2), (4, 58), (5, 56), (6, 6), (7, 7)]) (p' := 0x129644) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 1), (2, 2), (4, 58), (5, 56), (6, 6), (7, 7)]) (p' := 0x129648) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 1), (2, 2), (4, 58), (5, 56), (6, 6), (7, 7)]) (p' := 0x12964c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 1), (2, 2), (4, 58), (5, 56), (6, 6), (7, 7)]) (p' := 0x129650) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 1), (2, 2), (4, 58), (5, 56), (6, 6), (7, 7)]) (p' := 0x129653) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 62), (1, 1), (2, 2), (4, 58), (5, 56), (6, 6)]) (p' := 0x129657) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 62), (1, 1), (2, 2), (5, 56), (6, 6)]) (p' := 0x100a20) f12 (fun _ h => h.2) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 70) (by decide) (by decide) rfl rfl

theorem block_l12962f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12962f :=
  Rest.liftedBlock (rest_l12962f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12962f x hx)

theorem rest_l12965d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12965d bytes_l12965d) (entryMap (live .l12965d))
      19 0x12965d bytes_l12965d b_l12965d := by
  have f0 : InstrSpec 0x12965d [0x55] (PushPre 0x12965d 1) (pushR64Effect 0x12965d 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12965d 1 5).toInstrSpec (push_r64_effect_step 0x12965d 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x12965e [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x12965e) (movR64R64Effect 0x12965e 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x12965e 5 4).toInstrSpec (mov_r64_r64_effect_step 0x12965e 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129661 [0x48, 0x81, 0xEC, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129661) (subR64Imm32Effect 0x129661 4 0x80)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x129661 4 0x80).toInstrSpec (sub_r64_imm32_effect_step 0x129661 0x48 0xec 0x80 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129668 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x129668) (movR64R64Effect 0x129668 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x129668 0 2).toInstrSpec (mov_r64_r64_effect_step 0x129668 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12966b [0x48, 0x8B, 0x55, 0x18] (LoadPre 0x12966b (fun s => AddrMode.addr (.base 5 (.d8 0x18)) s (0x12966b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12966b 2 (.base 5 (.d8 0x18)))
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12966b 2 (.base 5 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x12966b 0x48 (by decide) 2 (.base 5 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x12966f [0x48, 0x89, 0x75, 0xF0] (StorePre 0x12966f 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x12966f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12966f 6 (.base 5 (.d8 0xf0)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12966f 6 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x12966f 0x48 (by decide) 6 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x129673 [0x48, 0x89, 0x45, 0xF8] (StorePre 0x129673 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x129673 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129673 0 (.base 5 (.d8 0xf8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129673 0 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x129673 0x48 (by decide) 0 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x129677 [0x48, 0x89, 0x4D, 0xE0] (StorePre 0x129677 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x129677 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129677 1 (.base 5 (.d8 0xe0)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129677 1 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x129677 0x48 (by decide) 1 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x12967b [0x4C, 0x89, 0x45, 0xE8] (StorePre 0x12967b 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x12967b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12967b 8 (.base 5 (.d8 0xe8)))
      [.gpr 8, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12967b 8 (.base 5 (.d8 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x12967b 0x4c (by decide) 0 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12967f [0x48, 0x8D, 0x05, 0x8A, 0xA6, 0x0D, 0x00] (fun s => s.RIP = 0x12967f) (leaR64Effect 0x12967f 0 (.rip 0xda68a))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x12967f 0 (.rip 0xda68a)).toInstrSpec (lea_r64_effect_step 0x12967f 0x48 (by decide) 0 (.rip 0xda68a) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129686 [0x40, 0x0F, 0xB6, 0xCF] (fun s => s.RIP = 0x129686) (movzxR32R8Effect 0x129686 4 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x129686 4 1 7).toInstrSpec (movzx_r32_r8_rex_effect_step 0x129686 0x40 (by decide) 0xcf (by decide)) pre_rip
  have f11 : InstrSpec 0x12968a [0x48, 0x63, 0x34, 0x88] (LoadPre 0x12968a (fun s => AddrMode.addr (.sib 0 (some 1) 2 .none) s (0x12968a + BitVec.ofNat 64 4)) 4) (movsxdR64M32Effect 0x12968a 4 6 (.sib 0 (some 1) 2 .none))
      [.gpr 0, .gpr 1] [] [.reg 6, .rip] :=
    (movsxdR64M32Effect_footprint 0x12968a 4 6 (.sib 0 (some 1) 2 .none)).toInstrSpec (movsxd_r64_m32_effect_step 0x12968a 0x48 (by decide) 6 (.sib 0 (some 1) 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x12968e [0x48, 0x01, 0xC6] (fun s => s.RIP = 0x12968e) (addR64R64Effect 0x12968e 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12968e 6 0).toInstrSpec (add_r64_r64_effect_step 0x12968e 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x129691 [0x48, 0x8D, 0x05, 0x88, 0xA6, 0x0D, 0x00] (fun s => s.RIP = 0x129691) (leaR64Effect 0x129691 0 (.rip 0xda688))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129691 0 (.rip 0xda688)).toInstrSpec (lea_r64_effect_step 0x129691 0x48 (by decide) 0 (.rip 0xda688) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x129698 [0x48, 0x8B, 0x04, 0xC8] (LoadPre 0x129698 (fun s => AddrMode.addr (.sib 0 (some 1) 3 .none) s (0x129698 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129698 0 (.sib 0 (some 1) 3 .none))
      [.gpr 0, .gpr 1] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x129698 0 (.sib 0 (some 1) 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x129698 0x48 (by decide) 0 (.sib 0 (some 1) 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x12969c [0x48, 0x89, 0x75, 0xD0] (StorePre 0x12969c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x12969c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12969c 6 (.base 5 (.d8 0xd0)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12969c 6 (.base 5 (.d8 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x12969c 0x48 (by decide) 6 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x1296a0 [0x48, 0x89, 0x45, 0xD8] (StorePre 0x1296a0 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x1296a0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296a0 0 (.base 5 (.d8 0xd8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296a0 0 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x1296a0 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x1296a4 [0x4D, 0x85, 0xC9] (fun s => s.RIP = 0x1296a4) (testR64R64Effect 0x1296a4 9 9)
      [.gpr 9, .gpr 9] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1296a4 9 9).toInstrSpec (test_r64_r64_effect_step 0x1296a4 0x4d 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x12965e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (4, 53), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x129661) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x129668) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x12966b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 1), (2, 61), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x12966f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 1), (2, 61), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x129673) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 1), (2, 61), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x129677) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 59), (1, 1), (2, 61), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x12967b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 1), (2, 61), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x12967f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 61), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x129686) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 69), (2, 61), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x12968a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 67), (1, 69), (2, 61), (4, 57), (5, 55), (6, 71), (7, 7), (8, 8), (9, 9)]) (p' := 0x12968e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 67), (1, 69), (2, 61), (4, 57), (5, 55), (6, 73), (7, 7), (8, 8), (9, 9)]) (p' := 0x129691) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 69), (2, 61), (4, 57), (5, 55), (6, 73), (7, 7), (8, 8), (9, 9)]) (p' := 0x129698) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 69), (2, 61), (4, 57), (5, 55), (6, 73), (7, 7), (8, 8), (9, 9)]) (p' := 0x12969c) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (1, 69), (2, 61), (4, 57), (5, 55), (6, 73), (7, 7), (8, 8), (9, 9)]) (p' := 0x1296a0) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 77), (1, 69), (2, 61), (4, 57), (5, 55), (6, 73), (7, 7), (8, 8), (9, 9)]) (p' := 0x1296a4) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f17 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 77), (1, 69), (2, 61), (4, 57), (5, 55), (6, 73), (7, 7), (8, 8), (9, 9), (19, 81)]) (p' := 0x1296a7) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 83) (jcc_rel8_effect_step 0x1296a7 5 0x42) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12965d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12965d :=
  Rest.liftedBlock (rest_l12965d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12965d x hx)

theorem rest_l1296a9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1296a9 bytes_l1296a9) (entryMap (live .l1296a9))
      14 0x1296a9 bytes_l1296a9 b_l1296a9 := by
  have f0 : InstrSpec 0x1296a9 [0x48, 0x8D, 0x45, 0xD0] (fun s => s.RIP = 0x1296a9) (leaR64Effect 0x1296a9 0 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1296a9 0 (.base 5 (.d8 0xd0))).toInstrSpec (lea_r64_effect_step 0x1296a9 0x48 (by decide) 0 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1296ad [0x48, 0x8D, 0x75, 0x80] (fun s => s.RIP = 0x1296ad) (leaR64Effect 0x1296ad 6 (.base 5 (.d8 0x80)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1296ad 6 (.base 5 (.d8 0x80))).toInstrSpec (lea_r64_effect_step 0x1296ad 0x48 (by decide) 6 (.base 5 (.d8 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1296b1 [0x48, 0x89, 0x06] (StorePre 0x1296b1 3 (fun s => AddrMode.addr (.base 6 .none) s (0x1296b1 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1296b1 0 (.base 6 .none))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296b1 0 (.base 6 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1296b1 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1296b4 [0x48, 0x8D, 0x05, 0xB5, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x1296b4) (leaR64Effect 0x1296b4 0 (.rip 0x9b5))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1296b4 0 (.rip 0x9b5)).toInstrSpec (lea_r64_effect_step 0x1296b4 0x48 (by decide) 0 (.rip 0x9b5) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1296bb [0x48, 0x89, 0x46, 0x08] (StorePre 0x1296bb 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1296bb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296bb 0 (.base 6 (.d8 0x8)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296bb 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1296bb 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1296bf [0x48, 0x8D, 0x45, 0xF0] (fun s => s.RIP = 0x1296bf) (leaR64Effect 0x1296bf 0 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1296bf 0 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x1296bf 0x48 (by decide) 0 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1296c3 [0x48, 0x89, 0x46, 0x10] (StorePre 0x1296c3 4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1296c3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296c3 0 (.base 6 (.d8 0x10)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296c3 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1296c3 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1296c7 [0x48, 0x8D, 0x05, 0x82, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x1296c7) (leaR64Effect 0x1296c7 0 (.rip 0x982))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1296c7 0 (.rip 0x982)).toInstrSpec (lea_r64_effect_step 0x1296c7 0x48 (by decide) 0 (.rip 0x982) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1296ce [0x48, 0x89, 0x46, 0x18] (StorePre 0x1296ce 4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1296ce + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296ce 0 (.base 6 (.d8 0x18)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296ce 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1296ce 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1296d2 [0x48, 0x8D, 0x4D, 0xE0] (fun s => s.RIP = 0x1296d2) (leaR64Effect 0x1296d2 1 (.base 5 (.d8 0xe0)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x1296d2 1 (.base 5 (.d8 0xe0))).toInstrSpec (lea_r64_effect_step 0x1296d2 0x48 (by decide) 1 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1296d6 [0x48, 0x89, 0x4E, 0x20] (StorePre 0x1296d6 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1296d6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296d6 1 (.base 6 (.d8 0x20)))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296d6 1 (.base 6 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1296d6 0x48 (by decide) 1 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1296da [0x48, 0x89, 0x46, 0x28] (StorePre 0x1296da 4 (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x1296da + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296da 0 (.base 6 (.d8 0x28)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296da 0 (.base 6 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1296da 0x48 (by decide) 0 (.base 6 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1296de [0x48, 0x8D, 0x3D, 0xAD, 0x83, 0x0D, 0x00] (fun s => s.RIP = 0x1296de) (leaR64Effect 0x1296de 7 (.rip 0xd83ad))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1296de 7 (.rip 0xd83ad)).toInstrSpec (lea_r64_effect_step 0x1296de 0x48 (by decide) 7 (.rip 0xd83ad) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1296e5 [0xFF, 0x15, 0xF5, 0xA6, 0x0D, 0x00] (GoesTo (CallMemPre 0x1296e5 (.rip 0xda6f5)) (callEffect (callMemPtr 0x1296e5 (.rip 0xda6f5)) (0x1296e5 + BitVec.ofNat 64 (callMemLen (.rip 0xda6f5)))) 0x129770) (callEffect (callMemPtr 0x1296e5 (.rip 0xda6f5)) (0x1296e5 + BitVec.ofNat 64 (callMemLen (.rip 0xda6f5))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1296e5 (.rip 0xda6f5)).toInstrSpec (call_m64_effect_step 0x1296e5 (.rip 0xda6f5) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (5, 5)]) (p' := 0x1296ad) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296b1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296b4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296bb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296bf) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296c3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296c7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296ce) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296d2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296d6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296da) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296de) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 4), (5, 5), (6, 55), (7, 71)]) (p' := 0x1296e5) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 73), (5, 5), (6, 55), (7, 71)]) (p' := 0x129770) f13 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l1296a9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1296a9 :=
  Rest.liftedBlock (rest_l1296a9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1296a9 x hx)

theorem rest_l1296eb_1 [Bindings] (code : CodeMap) :
    Rest (n := 83) code lifted (codeRange 0x1296eb bytes_l1296eb) [(0, 74), (1, 77), (2, 2), (4, 4), (5, 5), (6, 61), (7, 81), (9, 9)]
      1 0x129745 bytes_l1296eb_1 b_l1296eb_1 := by
  have f20 : InstrSpec 0x129745 [0xFF, 0x15, 0x95, 0xA6, 0x0D, 0x00] (GoesTo (CallMemPre 0x129745 (.rip 0xda695)) (callEffect (callMemPtr 0x129745 (.rip 0xda695)) (0x129745 + BitVec.ofNat 64 (callMemLen (.rip 0xda695)))) 0x129770) (callEffect (callMemPtr 0x129745 (.rip 0xda695)) (0x129745 + BitVec.ofNat 64 (callMemLen (.rip 0xda695))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x129745 (.rip 0xda695)).toInstrSpec (call_m64_effect_step 0x129745 (.rip 0xda695) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 74), (1, 77), (2, 2), (4, 83), (5, 5), (6, 61), (7, 81), (9, 9)]) (p' := 0x129770) f20 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem rest_l1296eb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1296eb bytes_l1296eb) (entryMap (live .l1296eb))
      21 0x1296eb bytes_l1296eb b_l1296eb := by
  have f0 : InstrSpec 0x1296eb [0x48, 0x8B, 0x45, 0x10] (LoadPre 0x1296eb (fun s => AddrMode.addr (.base 5 (.d8 0x10)) s (0x1296eb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1296eb 0 (.base 5 (.d8 0x10)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1296eb 0 (.base 5 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1296eb 0x48 (by decide) 0 (.base 5 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1296ef [0x48, 0x8D, 0x4D, 0xC0] (fun s => s.RIP = 0x1296ef) (leaR64Effect 0x1296ef 1 (.base 5 (.d8 0xc0)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x1296ef 1 (.base 5 (.d8 0xc0))).toInstrSpec (lea_r64_effect_step 0x1296ef 0x48 (by decide) 1 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1296f3 [0x4C, 0x89, 0x09] (StorePre 0x1296f3 3 (fun s => AddrMode.addr (.base 1 .none) s (0x1296f3 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1296f3 9 (.base 1 .none))
      [.gpr 9, .gpr 1] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296f3 9 (.base 1 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1296f3 0x4c (by decide) 1 (.base 1 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1296f6 [0x48, 0x89, 0x41, 0x08] (StorePre 0x1296f6 4 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x1296f6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296f6 0 (.base 1 (.d8 0x8)))
      [.gpr 0, .gpr 1] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296f6 0 (.base 1 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1296f6 0x48 (by decide) 0 (.base 1 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1296fa [0x48, 0x8D, 0x45, 0xD0] (fun s => s.RIP = 0x1296fa) (leaR64Effect 0x1296fa 0 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1296fa 0 (.base 5 (.d8 0xd0))).toInstrSpec (lea_r64_effect_step 0x1296fa 0x48 (by decide) 0 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1296fe [0x48, 0x8D, 0x75, 0x80] (fun s => s.RIP = 0x1296fe) (leaR64Effect 0x1296fe 6 (.base 5 (.d8 0x80)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1296fe 6 (.base 5 (.d8 0x80))).toInstrSpec (lea_r64_effect_step 0x1296fe 0x48 (by decide) 6 (.base 5 (.d8 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129702 [0x48, 0x89, 0x06] (StorePre 0x129702 3 (fun s => AddrMode.addr (.base 6 .none) s (0x129702 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x129702 0 (.base 6 .none))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x129702 0 (.base 6 .none)).toInstrSpec (mov_m64_r64_effect_step 0x129702 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x129705 [0x48, 0x8D, 0x05, 0x64, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x129705) (leaR64Effect 0x129705 0 (.rip 0x964))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129705 0 (.rip 0x964)).toInstrSpec (lea_r64_effect_step 0x129705 0x48 (by decide) 0 (.rip 0x964) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12970c [0x48, 0x89, 0x46, 0x08] (StorePre 0x12970c 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x12970c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12970c 0 (.base 6 (.d8 0x8)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x12970c 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x12970c 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x129710 [0x48, 0x89, 0x4E, 0x10] (StorePre 0x129710 4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x129710 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129710 1 (.base 6 (.d8 0x10)))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x129710 1 (.base 6 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x129710 0x48 (by decide) 1 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x129714 [0x48, 0x8D, 0x05, 0xE5, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x129714) (leaR64Effect 0x129714 0 (.rip 0x9e5))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129714 0 (.rip 0x9e5)).toInstrSpec (lea_r64_effect_step 0x129714 0x48 (by decide) 0 (.rip 0x9e5) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12971b [0x48, 0x89, 0x46, 0x18] (StorePre 0x12971b 4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x12971b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12971b 0 (.base 6 (.d8 0x18)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x12971b 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x12971b 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x12971f [0x48, 0x8D, 0x45, 0xF0] (fun s => s.RIP = 0x12971f) (leaR64Effect 0x12971f 0 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x12971f 0 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x12971f 0x48 (by decide) 0 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x129723 [0x48, 0x89, 0x46, 0x20] (StorePre 0x129723 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x129723 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129723 0 (.base 6 (.d8 0x20)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x129723 0 (.base 6 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x129723 0x48 (by decide) 0 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x129727 [0x48, 0x8D, 0x05, 0x22, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x129727) (leaR64Effect 0x129727 0 (.rip 0x922))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129727 0 (.rip 0x922)).toInstrSpec (lea_r64_effect_step 0x129727 0x48 (by decide) 0 (.rip 0x922) (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x12972e [0x48, 0x89, 0x46, 0x28] (StorePre 0x12972e 4 (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x12972e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12972e 0 (.base 6 (.d8 0x28)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x12972e 0 (.base 6 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x12972e 0x48 (by decide) 0 (.base 6 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x129732 [0x48, 0x8D, 0x4D, 0xE0] (fun s => s.RIP = 0x129732) (leaR64Effect 0x129732 1 (.base 5 (.d8 0xe0)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x129732 1 (.base 5 (.d8 0xe0))).toInstrSpec (lea_r64_effect_step 0x129732 0x48 (by decide) 1 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x129736 [0x48, 0x89, 0x4E, 0x30] (StorePre 0x129736 4 (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x129736 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129736 1 (.base 6 (.d8 0x30)))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x129736 1 (.base 6 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x129736 0x48 (by decide) 1 (.base 6 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x12973a [0x48, 0x89, 0x46, 0x38] (StorePre 0x12973a 4 (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x12973a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12973a 0 (.base 6 (.d8 0x38)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x12973a 0 (.base 6 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x12973a 0x48 (by decide) 0 (.base 6 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x12973e [0x48, 0x8D, 0x3D, 0x84, 0x83, 0x0D, 0x00] (fun s => s.RIP = 0x12973e) (leaR64Effect 0x12973e 7 (.rip 0xd8384))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x12973e 7 (.rip 0xd8384)).toInstrSpec (lea_r64_effect_step 0x12973e 0x48 (by decide) 7 (.rip 0xd8384) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (5, 5), (9, 9)]) (p' := 0x1296ef) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (4, 4), (5, 5), (9, 9)]) (p' := 0x1296f3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (2, 2), (4, 4), (5, 5), (9, 9)]) (p' := 0x1296f6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (4, 4), (5, 5), (9, 9)]) (p' := 0x1296fa) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (2, 2), (4, 4), (5, 5), (9, 9)]) (p' := 0x1296fe) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x129702) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x129705) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x12970c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x129710) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x129714) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x12971b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x12971f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x129723) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x129727) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x12972e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 74), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x129732) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 74), (1, 77), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x129736) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 74), (1, 77), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x12973a) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 74), (1, 77), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x12973e) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f19 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 74), (1, 77), (2, 2), (4, 4), (5, 5), (6, 61), (7, 81), (9, 9)]) (p' := 0x129745) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1296eb_1 code

theorem block_l1296eb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1296eb :=
  Rest.liftedBlock (rest_l1296eb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1296eb x hx)

theorem rest_l12974b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12974b bytes_l12974b) (entryMap (live .l12974b))
      5 0x12974b bytes_l12974b b_l12974b := by
  have f0 : InstrSpec 0x12974b [0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x12974b) (fun _ => nopEffect 0x12974b 5)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12974b 5).toInstrSpec (nop_m_effect_step 0x12974b [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129750 [0x55] (PushPre 0x129750 1) (pushR64Effect 0x129750 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129750 1 5).toInstrSpec (push_r64_effect_step 0x129750 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x129751 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129751) (movR64R64Effect 0x129751 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129751 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129751 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129754 [0x48, 0x8D, 0x34, 0x75, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129754) (leaR64Effect 0x129754 6 (.abs (some 6) 1 0x1))
      [.gpr 6] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x129754 6 (.abs (some 6) 1 0x1)).toInstrSpec (lea_r64_effect_step 0x129754 0x48 (by decide) 6 (.abs (some 6) 1 0x1) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12975c [0xFF, 0x15, 0x7E, 0xA6, 0x0D, 0x00] (GoesTo (CallMemPre 0x12975c (.rip 0xda67e)) (callEffect (callMemPtr 0x12975c (.rip 0xda67e)) (0x12975c + BitVec.ofNat 64 (callMemLen (.rip 0xda67e)))) 0x129770) (callEffect (callMemPtr 0x12975c (.rip 0xda67e)) (0x12975c + BitVec.ofNat 64 (callMemLen (.rip 0xda67e))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x12975c (.rip 0xda67e)).toInstrSpec (call_m64_effect_step 0x12975c (.rip 0xda67e) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x129750) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (4, 54), (5, 5), (6, 6), (7, 7)]) (p' := 0x129751) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (4, 54), (5, 56), (6, 6), (7, 7)]) (p' := 0x129754) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 2), (4, 54), (5, 56), (6, 58), (7, 7)]) (p' := 0x12975c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 2), (4, 60), (5, 56), (6, 58), (7, 7)]) (p' := 0x129770) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l12974b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12974b :=
  Rest.liftedBlock (rest_l12974b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12974b x hx)

theorem rest_l129762 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129762 bytes_l129762) (entryMap (live .l129762))
      2 0x129762 bytes_l129762 b_l129762 := by
  have f0 : InstrSpec 0x129762 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129762) (fun _ => nopEffect 0x129762 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x129762 10).toInstrSpec (nop_m_effect_step 0x129762 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12976c [0x0F, 0x1F, 0x40, 0x00] (fun s => s.RIP = 0x12976c) (fun _ => nopEffect 0x12976c 4)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12976c 4).toInstrSpec (nop_m_effect_step 0x12976c [] (by decide) (by decide) (.base 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x12976c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x129770) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l129762 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129762 :=
  Rest.liftedBlock (rest_l129762 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129762 x hx)

theorem rest_l129770 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129770 bytes_l129770) (entryMap (live .l129770))
      11 0x129770 bytes_l129770 b_l129770 := by
  have f0 : InstrSpec 0x129770 [0x55] (PushPre 0x129770 1) (pushR64Effect 0x129770 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129770 1 5).toInstrSpec (push_r64_effect_step 0x129770 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129771 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129771) (movR64R64Effect 0x129771 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129771 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129771 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129774 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x129774) (subR64Imm8Effect 0x129774 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x129774 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x129774 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129778 [0x48, 0x89, 0x7D, 0xF0] (StorePre 0x129778 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x129778 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129778 7 (.base 5 (.d8 0xf0)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129778 7 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x129778 0x48 (by decide) 7 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12977c [0x48, 0x89, 0x75, 0xF8] (StorePre 0x12977c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x12977c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12977c 6 (.base 5 (.d8 0xf8)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12977c 6 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x12977c 0x48 (by decide) 6 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x129780 [0x48, 0x8D, 0x45, 0xF0] (fun s => s.RIP = 0x129780) (leaR64Effect 0x129780 0 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129780 0 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x129780 0x48 (by decide) 0 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129784 [0x48, 0x89, 0x45, 0xD8] (StorePre 0x129784 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x129784 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129784 0 (.base 5 (.d8 0xd8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129784 0 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x129784 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x129788 [0x48, 0x89, 0x55, 0xE0] (StorePre 0x129788 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x129788 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129788 2 (.base 5 (.d8 0xe0)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129788 2 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x129788 0x48 (by decide) 2 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x12978c [0x66, 0xC7, 0x45, 0xE8, 0x01, 0x00] (StorePre 0x12978c 6 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x12978c + BitVec.ofNat 64 6)) 2) (movM16Imm16Effect 0x12978c (.base 5 (.d8 0xe8)) 0x1)
      [.gpr 5] [] [.rip] :=
    (movM16Imm16Effect_footprint 0x12978c (.base 5 (.d8 0xe8)) 0x1).toInstrSpec (mov_m16_imm16_effect_step 0x12978c (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x129792 [0x48, 0x8D, 0x7D, 0xD8] (fun s => s.RIP = 0x129792) (leaR64Effect 0x129792 7 (.base 5 (.d8 0xd8)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x129792 7 (.base 5 (.d8 0xd8))).toInstrSpec (lea_r64_effect_step 0x129792 0x48 (by decide) 7 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129796 [0xFF, 0x15, 0x84, 0xA6, 0x0D, 0x00] (GoesTo (CallMemPre 0x129796 (.rip 0xda684)) (callEffect (callMemPtr 0x129796 (.rip 0xda684)) (0x129796 + BitVec.ofNat 64 (callMemLen (.rip 0xda684)))) 0x100a20) (callEffect (callMemPtr 0x129796 (.rip 0xda684)) (0x129796 + BitVec.ofNat 64 (callMemLen (.rip 0xda684))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x129796 (.rip 0xda684)).toInstrSpec (call_m64_effect_step 0x129796 (.rip 0xda684) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x100a20
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 53), (5, 5), (6, 6), (7, 7)]) (p' := 0x129771) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 53), (5, 55), (6, 6), (7, 7)]) (p' := 0x129774) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129778) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x12977c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129780) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129784) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129788) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x12978c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129792) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6)]) (p' := 0x129796) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 61), (2, 2), (5, 55), (6, 6)]) (p' := 0x100a20) f10 (fun _ h => h.2) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l129770 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129770 :=
  Rest.liftedBlock (rest_l129770 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129770 x hx)

theorem rest_l12979c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12979c bytes_l12979c) (entryMap (live .l12979c))
      1 0x12979c bytes_l12979c b_l12979c := by
  have f0 : InstrSpec 0x12979c [0x0F, 0x1F, 0x40, 0x00] (fun s => s.RIP = 0x12979c) (fun _ => nopEffect 0x12979c 4)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12979c 4).toInstrSpec (nop_m_effect_step 0x12979c [] (by decide) (by decide) (.base 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297a0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l12979c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12979c :=
  Rest.liftedBlock (rest_l12979c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12979c x hx)

theorem rest_l129c30 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c30 bytes_l129c30) (entryMap (live .l129c30))
      12 0x129c30 bytes_l129c30 b_l129c30 := by
  have f0 : InstrSpec 0x129c30 [0x55] (PushPre 0x129c30 1) (pushR64Effect 0x129c30 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129c30 1 5).toInstrSpec (push_r64_effect_step 0x129c30 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129c31 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129c31) (movR64R64Effect 0x129c31 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129c31 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129c31 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129c34 [0x41, 0x57] (PushPre 0x129c34 2) (pushR64Effect 0x129c34 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129c34 2 15).toInstrSpec (push_r64_rex_effect_step 0x129c34 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x129c36 [0x41, 0x56] (PushPre 0x129c36 2) (pushR64Effect 0x129c36 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129c36 2 14).toInstrSpec (push_r64_rex_effect_step 0x129c36 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x129c38 [0x41, 0x54] (PushPre 0x129c38 2) (pushR64Effect 0x129c38 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129c38 2 12).toInstrSpec (push_r64_rex_effect_step 0x129c38 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x129c3a [0x53] (PushPre 0x129c3a 1) (pushR64Effect 0x129c3a 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129c3a 1 3).toInstrSpec (push_r64_effect_step 0x129c3a 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x129c3b [0x4C, 0x89, 0xC3] (fun s => s.RIP = 0x129c3b) (movR64R64Effect 0x129c3b 3 8)
      [.gpr 8] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x129c3b 3 8).toInstrSpec (mov_r64_r64_effect_step 0x129c3b 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x129c3e [0x49, 0x89, 0xCE] (fun s => s.RIP = 0x129c3e) (movR64R64Effect 0x129c3e 14 1)
      [.gpr 1] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x129c3e 14 1).toInstrSpec (mov_r64_r64_effect_step 0x129c3e 0x49 0xce (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x129c41 [0x49, 0x89, 0xF4] (fun s => s.RIP = 0x129c41) (movR64R64Effect 0x129c41 12 6)
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x129c41 12 6).toInstrSpec (mov_r64_r64_effect_step 0x129c41 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x129c44 [0x49, 0x89, 0xFF] (fun s => s.RIP = 0x129c44) (movR64R64Effect 0x129c44 15 7)
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x129c44 15 7).toInstrSpec (mov_r64_r64_effect_step 0x129c44 0x49 0xff (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129c47 [0x83, 0xFA, 0xFF] (fun s => s.RIP = 0x129c47) (cmpR32Imm8Effect 0x129c47 3 2 0xff)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x129c47 3 2 0xff).toInstrSpec (cmp_r32_imm8_effect_step 0x129c47 0xfa 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c31) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c34) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c36) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c38) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 60), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c3a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c3b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c3e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 66), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c41) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 68), (13, 13), (14, 66), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c44) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 68), (13, 13), (14, 66), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c47) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 68), (13, 13), (14, 66), (15, 70), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c4a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 74) (jcc_rel8_effect_step 0x129c4a 4 0x12) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129c30 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c30 :=
  Rest.liftedBlock (rest_l129c30 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c30 x hx)

theorem rest_l129c4c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c4c bytes_l129c4c) (entryMap (live .l129c4c))
      2 0x129c4c bytes_l129c4c b_l129c4c := by
  have f0 : InstrSpec 0x129c4c [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x129c4c) (movR64R64Effect 0x129c4c 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x129c4c 7 15).toInstrSpec (mov_r64_r64_effect_step 0x129c4c 0x4c 0xff (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129c4f [0x89, 0xD6] (fun s => s.RIP = 0x129c4f) (movR32R32Effect 0x129c4f 2 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x129c4f 2 6 2).toInstrSpec (mov_r32_r32_effect_step 0x129c4f 0xd6 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (15, 15)]) (p' := 0x129c4f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (15, 15)]) (p' := 0x129c51) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l129c4c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c4c :=
  Rest.liftedBlock (rest_l129c4c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c4c x hx)

theorem rest_l129c56 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c56 bytes_l129c56) (entryMap (live .l129c56))
      4 0x129c56 bytes_l129c56 b_l129c56 := by
  have f0 : InstrSpec 0x129c56 [0x89, 0xC1] (fun s => s.RIP = 0x129c56) (movR32R32Effect 0x129c56 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x129c56 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x129c56 0xc1 (by decide)) pre_rip
  have f1 : InstrSpec 0x129c58 [0xB0, 0x01] (fun s => s.RIP = 0x129c58) (movR8Imm8Effect 0x129c58 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x129c58 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x129c58 0xb0 (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x129c5a [0x84, 0xC9] (fun s => s.RIP = 0x129c5a) (testR8R8Effect 0x129c5a 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x129c5a 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x129c5a 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c58) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c5a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c5c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x129c5c 5 0x1f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129c56 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c56 :=
  Rest.liftedBlock (rest_l129c56 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c56 x hx)

theorem rest_l129c5e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c5e bytes_l129c5e) (entryMap (live .l129c5e))
      2 0x129c5e bytes_l129c5e b_l129c5e := by
  have f0 : InstrSpec 0x129c5e [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x129c5e) (testR64R64Effect 0x129c5e 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x129c5e 14 14).toInstrSpec (test_r64_r64_effect_step 0x129c5e 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c61) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x129c61 4 0x18) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129c5e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c5e :=
  Rest.liftedBlock (rest_l129c5e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c5e x hx)

theorem rest_l129c63 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c63 bytes_l129c63) (entryMap (live .l129c63))
      9 0x129c63 bytes_l129c63 b_l129c63 := by
  have f0 : InstrSpec 0x129c63 [0x49, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x129c63 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x129c63 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x129c63 0 (.sib 12 none 0 (.d8 0x18)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x129c63 0 (.sib 12 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x129c63 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x129c68 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x129c68) (movR64R64Effect 0x129c68 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x129c68 7 15).toInstrSpec (mov_r64_r64_effect_step 0x129c68 0x4c 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129c6b [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x129c6b) (movR64R64Effect 0x129c6b 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x129c6b 6 14).toInstrSpec (mov_r64_r64_effect_step 0x129c6b 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129c6e [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x129c6e) (movR64R64Effect 0x129c6e 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x129c6e 2 3).toInstrSpec (mov_r64_r64_effect_step 0x129c6e 0x48 0xda (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129c71 [0x5B] (PopPre 0x129c71) (popR64Effect 0x129c71 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c71 1 3).toInstrSpec (pop_r64_effect_step 0x129c71 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x129c72 [0x41, 0x5C] (PopPre 0x129c72) (popR64Effect 0x129c72 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c72 2 12).toInstrSpec (pop_r64_rex_effect_step 0x129c72 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x129c74 [0x41, 0x5E] (PopPre 0x129c74) (popR64Effect 0x129c74 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c74 2 14).toInstrSpec (pop_r64_rex_effect_step 0x129c74 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x129c76 [0x41, 0x5F] (PopPre 0x129c76) (popR64Effect 0x129c76 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c76 2 15).toInstrSpec (pop_r64_rex_effect_step 0x129c76 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x129c78 [0x5D] (PopPre 0x129c78) (popR64Effect 0x129c78 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c78 1 5).toInstrSpec (pop_r64_effect_step 0x129c78 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (12, 12), (14, 14), (15, 15)]) (p' := 0x129c68) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (12, 12), (14, 14), (15, 15)]) (p' := 0x129c6b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (12, 12), (14, 14), (15, 15)]) (p' := 0x129c6e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (12, 12), (14, 14), (15, 15)]) (p' := 0x129c71) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(4, 57), (12, 12), (14, 14), (15, 15)]) (p' := 0x129c72) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(4, 59), (14, 14), (15, 15)]) (p' := 0x129c74) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(4, 61), (15, 15)]) (p' := 0x129c76) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(4, 63)]) (p' := 0x129c78) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := []) (p' := 0x129c79) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l129c63 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c63 :=
  Rest.liftedBlock (rest_l129c63 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c63 x hx)

theorem rest_l129c7b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c7b bytes_l129c7b) (entryMap (live .l129c7b))
      1 0x129c7b bytes_l129c7b b_l129c7b := by
  have f0 : InstrSpec 0x129c7b [0x31, 0xC0] (fun s => s.RIP = 0x129c7b) (xorR32R32Effect 0x129c7b 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129c7b 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x129c7b 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c7d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l129c7b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c7b :=
  Rest.liftedBlock (rest_l129c7b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c7b x hx)

theorem rest_l129c7d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c7d bytes_l129c7d) (entryMap (live .l129c7d))
      6 0x129c7d bytes_l129c7d b_l129c7d := by
  have f0 : InstrSpec 0x129c7d [0x5B] (PopPre 0x129c7d) (popR64Effect 0x129c7d 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c7d 1 3).toInstrSpec (pop_r64_effect_step 0x129c7d 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129c7e [0x41, 0x5C] (PopPre 0x129c7e) (popR64Effect 0x129c7e 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c7e 2 12).toInstrSpec (pop_r64_rex_effect_step 0x129c7e 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x129c80 [0x41, 0x5E] (PopPre 0x129c80) (popR64Effect 0x129c80 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c80 2 14).toInstrSpec (pop_r64_rex_effect_step 0x129c80 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x129c82 [0x41, 0x5F] (PopPre 0x129c82) (popR64Effect 0x129c82 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c82 2 15).toInstrSpec (pop_r64_rex_effect_step 0x129c82 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x129c84 [0x5D] (PopPre 0x129c84) (popR64Effect 0x129c84 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c84 1 5).toInstrSpec (pop_r64_effect_step 0x129c84 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x129c85 [0xC3] (RetPre 0x129c85) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x129c85).toInstrSpec (ret_effect_step 0x129c85) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 54), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c7e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 57) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 57), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 56), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c80) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 60), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 56), (13, 13), (14, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c82) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 63), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 56), (13, 13), (14, 59), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c84) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 66), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 56), (13, 13), (14, 59), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c85) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 69), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 56), (13, 13), (14, 59), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l129c7d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c7d :=
  Rest.liftedBlock (rest_l129c7d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c7d x hx)

theorem rest_l12a050 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a050 bytes_l12a050) (entryMap (live .l12a050))
      4 0x12a050 bytes_l12a050 b_l12a050 := by
  have f0 : InstrSpec 0x12a050 [0x48, 0x8B, 0x07] (LoadPre 0x12a050 (fun s => AddrMode.addr (.base 7 .none) s (0x12a050 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a050 0 (.base 7 .none))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12a050 0 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a050 0x48 (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12a053 [0x48, 0x8B, 0x4F, 0x08] (LoadPre 0x12a053 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x12a053 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a053 1 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12a053 1 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12a053 0x48 (by decide) 1 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12a057 [0x48, 0x8B, 0x49, 0x18] (LoadPre 0x12a057 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x12a057 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a057 1 (.base 1 (.d8 0x18)))
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12a057 1 (.base 1 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x12a057 0x48 (by decide) 1 (.base 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12a05b [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x12a05b) (movR64R64Effect 0x12a05b 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12a05b 7 0).toInstrSpec (mov_r64_r64_effect_step 0x12a05b 0x48 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (7, 7)]) (p' := 0x12a053) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (7, 7)]) (p' := 0x12a057) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (7, 7)]) (p' := 0x12a05b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53)]) (p' := 0x12a05e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l12a050 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a050 :=
  Rest.liftedBlock (rest_l12a050 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a050 x hx)

theorem rest_l12a070 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a070 bytes_l12a070) (entryMap (live .l12a070))
      5 0x12a070 bytes_l12a070 b_l12a070 := by
  have f0 : InstrSpec 0x12a070 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x12a070) (movR64R64Effect 0x12a070 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12a070 0 6).toInstrSpec (mov_r64_r64_effect_step 0x12a070 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a073 [0x48, 0x8B, 0x37] (LoadPre 0x12a073 (fun s => AddrMode.addr (.base 7 .none) s (0x12a073 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a073 6 (.base 7 .none))
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12a073 6 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a073 0x48 (by decide) 6 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12a076 [0x48, 0x8B, 0x57, 0x08] (LoadPre 0x12a076 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x12a076 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a076 2 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12a076 2 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12a076 0x48 (by decide) 2 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12a07a [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x12a07a) (movR64R64Effect 0x12a07a 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12a07a 7 0).toInstrSpec (mov_r64_r64_effect_step 0x12a07a 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a07d [0xFF, 0x25, 0x85, 0x9D, 0x0D, 0x00] (GoesTo (JmpMemPre 0x12a07d 6 (.rip 0xd9d85)) (jmpM64Effect 0x12a07d 6 (.rip 0xd9d85)) 0x129100) (jmpM64Effect 0x12a07d 6 (.rip 0xd9d85))
      [] [] [.rip] :=
    ((jmpM64Effect_footprint 0x12a07d 6 (.rip 0xd9d85)).toInstrSpec (jmp_m64_effect_step 0x12a07d (.rip 0xd9d85) (by decide) (by decide) (by decide)) (JmpMemPre.of_addr rfl)).goesTo 0x129100
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a073) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a076) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a07a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a07d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129100) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 62) (by decide) rfl

theorem block_l12a070 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a070 :=
  Rest.liftedBlock (rest_l12a070 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a070 x hx)

theorem rest_l12a100 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a100 bytes_l12a100) (entryMap (live .l12a100))
      6 0x12a100 bytes_l12a100 b_l12a100 := by
  have f0 : InstrSpec 0x12a100 [0x48, 0x8B, 0x06] (LoadPre 0x12a100 (fun s => AddrMode.addr (.base 6 .none) s (0x12a100 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a100 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12a100 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a100 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12a103 [0x48, 0x8B, 0x76, 0x08] (LoadPre 0x12a103 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x12a103 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a103 6 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12a103 6 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12a103 0x48 (by decide) 6 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12a107 [0x48, 0x8B, 0x17] (LoadPre 0x12a107 (fun s => AddrMode.addr (.base 7 .none) s (0x12a107 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a107 2 (.base 7 .none))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12a107 2 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a107 0x48 (by decide) 2 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12a10a [0x48, 0x8B, 0x4F, 0x08] (LoadPre 0x12a10a (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x12a10a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a10a 1 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12a10a 1 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12a10a 0x48 (by decide) 1 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x12a10e [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x12a10e) (movR64R64Effect 0x12a10e 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12a10e 7 0).toInstrSpec (mov_r64_r64_effect_step 0x12a10e 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12a111 [0xFF, 0x25, 0x11, 0x9D, 0x0D, 0x00] (GoesTo (JmpMemPre 0x12a111 6 (.rip 0xd9d11)) (jmpM64Effect 0x12a111 6 (.rip 0xd9d11)) 0x1293a0) (jmpM64Effect 0x12a111 6 (.rip 0xd9d11))
      [] [] [.rip] :=
    ((jmpM64Effect_footprint 0x12a111 6 (.rip 0xd9d11)).toInstrSpec (jmp_m64_effect_step 0x12a111 (.rip 0xd9d11) (by decide) (by decide) (by decide)) (JmpMemPre.of_addr rfl)).goesTo 0x1293a0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a103) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a107) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a10a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a10e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 61), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a111) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 61), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293a0) f5 (fun _ h => h.2) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 64) (by decide) rfl

theorem block_l12a100 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a100 :=
  Rest.liftedBlock (rest_l12a100 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a100 x hx)

theorem rest_l12a430 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a430 bytes_l12a430) (entryMap (live .l12a430))
      10 0x12a430 bytes_l12a430 b_l12a430 := by
  have f0 : InstrSpec 0x12a430 [0x55] (PushPre 0x12a430 1) (pushR64Effect 0x12a430 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12a430 1 5).toInstrSpec (push_r64_effect_step 0x12a430 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x12a431 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x12a431) (movR64R64Effect 0x12a431 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x12a431 5 4).toInstrSpec (mov_r64_r64_effect_step 0x12a431 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a434 [0x53] (PushPre 0x12a434 1) (pushR64Effect 0x12a434 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12a434 1 3).toInstrSpec (push_r64_effect_step 0x12a434 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x12a435 [0x48, 0x83, 0xEC, 0x18] (fun s => s.RIP = 0x12a435) (subR64Imm8Effect 0x12a435 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x12a435 4 0x18).toInstrSpec (sub_r64_imm8_effect_step 0x12a435 0x48 0xec 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a439 [0x4C, 0x8B, 0x07] (LoadPre 0x12a439 (fun s => AddrMode.addr (.base 7 .none) s (0x12a439 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a439 8 (.base 7 .none))
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x12a439 8 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a439 0x4c (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x12a43c [0xB8, 0x14, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a43c) (movR32Imm32Effect 0x12a43c 5 0 0x14)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x12a43c 5 0 0x14).toInstrSpec (mov_r32_imm32_effect_step 0x12a43c 0xb8 (by decide) 0x14) pre_rip
  have f6 : InstrSpec 0x12a441 [0x48, 0x8D, 0x3D, 0xFB, 0x97, 0x0D, 0x00] (fun s => s.RIP = 0x12a441) (leaR64Effect 0x12a441 7 (.rip 0xd97fb))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x12a441 7 (.rip 0xd97fb)).toInstrSpec (lea_r64_effect_step 0x12a441 0x48 (by decide) 7 (.rip 0xd97fb) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12a448 [0x4C, 0x89, 0xC2] (fun s => s.RIP = 0x12a448) (movR64R64Effect 0x12a448 2 8)
      [.gpr 8] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12a448 2 8).toInstrSpec (mov_r64_r64_effect_step 0x12a448 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12a44b [0x49, 0x81, 0xF8, 0xE8, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x12a44b) (cmpR64Imm32Effect 0x12a44b 8 0x3e8)
      [.gpr 8] [] [.flags, .rip] :=
    (cmpR64Imm32Effect_footprint 0x12a44b 8 0x3e8).toInstrSpec (cmp_r64_imm32_effect_step 0x12a44b 0x49 0xf8 0x3e8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a431) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 53), (5, 55), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a434) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a435) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a439) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (8, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a43c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 1), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (8, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a441) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 63), (1, 1), (3, 3), (4, 59), (5, 55), (6, 6), (7, 65), (8, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a448) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 63), (1, 1), (2, 67), (3, 3), (4, 59), (5, 55), (6, 6), (7, 65), (8, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a44b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 63), (1, 1), (2, 67), (3, 3), (4, 59), (5, 55), (6, 6), (7, 65), (8, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a452) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 71) (jcc_rel8_effect_step 0x12a452 2 0x6d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a430 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a430 :=
  Rest.liftedBlock (rest_l12a430 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a430 x hx)

theorem rest_l12a454 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a454 bytes_l12a454) (entryMap (live .l12a454))
      3 0x12a454 bytes_l12a454 b_l12a454 := by
  have f0 : InstrSpec 0x12a454 [0x49, 0xB9, 0x4B, 0x59, 0x86, 0x38, 0xD6, 0xC5, 0x6D, 0x34] (fun s => s.RIP = 0x12a454) (movR64Imm64Effect 0x12a454 9 0x346dc5d63886594b)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x12a454 9 0x346dc5d63886594b).toInstrSpec (mov_r64_imm64_effect_step 0x12a454 0x49 0xb9 (by decide) (by decide) 0x346dc5d63886594b) pre_rip
  have f1 : InstrSpec 0x12a45e [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x12a45e) (movR64R64Effect 0x12a45e 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a45e 1 8).toInstrSpec (mov_r64_r64_effect_step 0x12a45e 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a461 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a461) (fun _ => nopEffect 0x12a461 15)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12a461 15).toInstrSpec (nop_m_effect_step 0x12a461 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a45e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a461) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a470) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l12a454 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a454 :=
  Rest.liftedBlock (rest_l12a454 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a454 x hx)

theorem rest_l12a470 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a470 bytes_l12a470) (entryMap (live .l12a470))
      20 0x12a470 bytes_l12a470 b_l12a470 := by
  have f0 : InstrSpec 0x12a470 [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x12a470) (movR64R64Effect 0x12a470 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x12a470 10 0).toInstrSpec (mov_r64_r64_effect_step 0x12a470 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a473 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x12a473) (movR64R64Effect 0x12a473 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12a473 0 1).toInstrSpec (mov_r64_r64_effect_step 0x12a473 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a476 [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x12a476) (mulR64Effect 0x12a476 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x12a476 9).toInstrSpec (mul_r64_effect_step 0x12a476 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12a479 [0x48, 0xC1, 0xEA, 0x0B] (fun s => s.RIP = 0x12a479) (shrR64Effect 0x12a479 4 2 11)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x12a479 4 2 11).toInstrSpec (shr_r64_imm8_effect_step 0x12a479 0x48 0xea 0xb (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a47d [0x69, 0xC2, 0x10, 0x27, 0x00, 0x00] (fun s => s.RIP = 0x12a47d) (imulR32R32Imm32Effect 0x12a47d 6 0 2 0x2710)
      [.gpr 2] [] [.reg 0, .flags, .rip] :=
    (imulR32R32Imm32Effect_footprint 0x12a47d 6 0 2 0x2710).toInstrSpec (imul_r32_r32_imm32_effect_step 0x12a47d 0xc2 (by decide) 0x2710) pre_rip
  have f5 : InstrSpec 0x12a483 [0x41, 0x89, 0xCB] (fun s => s.RIP = 0x12a483) (movR32R32Effect 0x12a483 3 11 1)
      [.gpr 1] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x12a483 3 11 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x12a483 0x41 0xcb (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12a486 [0x41, 0x29, 0xC3] (fun s => s.RIP = 0x12a486) (subR32R32Effect 0x12a486 3 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (subR32R32Effect_footprint 0x12a486 3 11 0).toInstrSpec (sub_r32_r32_rex_effect_step 0x12a486 0x41 0xc3 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12a489 [0x41, 0x69, 0xC3, 0x7B, 0x14, 0x00, 0x00] (fun s => s.RIP = 0x12a489) (imulR32R32Imm32Effect 0x12a489 7 0 11 0x147b)
      [.gpr 11] [] [.reg 0, .flags, .rip] :=
    (imulR32R32Imm32Effect_footprint 0x12a489 7 0 11 0x147b).toInstrSpec (imul_r32_r32_imm32_rex_effect_step 0x12a489 0x41 (by decide) 0xc3 (by decide) 0x147b) pre_rip
  have f8 : InstrSpec 0x12a490 [0xC1, 0xE8, 0x13] (fun s => s.RIP = 0x12a490) (shrR32Effect 0x12a490 3 0 19)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a490 3 0 19).toInstrSpec (shr_r32_imm8_effect_step 0x12a490 0xe8 0x13 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x12a493 [0x6B, 0xD8, 0x64] (fun s => s.RIP = 0x12a493) (imulR32R32Imm8Effect 0x12a493 3 3 0 0x64)
      [.gpr 0] [] [.reg 3, .flags, .rip] :=
    (imulR32R32Imm8Effect_footprint 0x12a493 3 3 0 0x64).toInstrSpec (imul_r32_r32_imm8_effect_step 0x12a493 0xd8 (by decide) 0x64) pre_rip
  have f10 : InstrSpec 0x12a496 [0x41, 0x29, 0xDB] (fun s => s.RIP = 0x12a496) (subR32R32Effect 0x12a496 3 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (subR32R32Effect_footprint 0x12a496 3 11 3).toInstrSpec (sub_r32_r32_rex_effect_step 0x12a496 0x41 0xdb (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12a499 [0x0F, 0xB7, 0x04, 0x47] (LoadPre 0x12a499 (fun s => AddrMode.addr (.sib 7 (some 0) 1 .none) s (0x12a499 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x12a499 4 0 (.sib 7 (some 0) 1 .none))
      [.gpr 7, .gpr 0] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x12a499 4 0 (.sib 7 (some 0) 1 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x12a499 0 (.sib 7 (some 0) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x12a49d [0x66, 0x42, 0x89, 0x44, 0x15, 0xE0] (StorePre 0x12a49d 6 (fun s => AddrMode.addr (.sib 5 (some 10) 0 (.d8 0xe0)) s (0x12a49d + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x12a49d 6 0 (.sib 5 (some 10) 0 (.d8 0xe0)))
      [.gpr 0, .gpr 5, .gpr 10] [] [.rip] :=
    (movM16R16Effect_footprint 0x12a49d 6 0 (.sib 5 (some 10) 0 (.d8 0xe0))).toInstrSpec (mov_m16_r16_rex_effect_step 0x12a49d 0x42 (by decide) 0 (.sib 5 (some 10) 0 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x12a4a3 [0x41, 0x0F, 0xB7, 0xC3] (fun s => s.RIP = 0x12a4a3) (movzxR32R16Effect 0x12a4a3 4 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movzxR32R16Effect_footprint 0x12a4a3 4 0 11).toInstrSpec (movzx_r32_r16_rex_effect_step 0x12a4a3 0x41 (by decide) 0xc3 (by decide)) pre_rip
  have f14 : InstrSpec 0x12a4a7 [0x0F, 0xB7, 0x04, 0x47] (LoadPre 0x12a4a7 (fun s => AddrMode.addr (.sib 7 (some 0) 1 .none) s (0x12a4a7 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x12a4a7 4 0 (.sib 7 (some 0) 1 .none))
      [.gpr 7, .gpr 0] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x12a4a7 4 0 (.sib 7 (some 0) 1 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x12a4a7 0 (.sib 7 (some 0) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x12a4ab [0x66, 0x42, 0x89, 0x44, 0x15, 0xE2] (StorePre 0x12a4ab 6 (fun s => AddrMode.addr (.sib 5 (some 10) 0 (.d8 0xe2)) s (0x12a4ab + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x12a4ab 6 0 (.sib 5 (some 10) 0 (.d8 0xe2)))
      [.gpr 0, .gpr 5, .gpr 10] [] [.rip] :=
    (movM16R16Effect_footprint 0x12a4ab 6 0 (.sib 5 (some 10) 0 (.d8 0xe2))).toInstrSpec (mov_m16_r16_rex_effect_step 0x12a4ab 0x42 (by decide) 0 (.sib 5 (some 10) 0 (.d8 0xe2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x12a4b1 [0x49, 0x8D, 0x42, 0xFC] (fun s => s.RIP = 0x12a4b1) (leaR64Effect 0x12a4b1 0 (.base 10 (.d8 0xfc)))
      [.gpr 10] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x12a4b1 0 (.base 10 (.d8 0xfc))).toInstrSpec (lea_r64_effect_step 0x12a4b1 0x49 (by decide) 0 (.base 10 (.d8 0xfc)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x12a4b5 [0x48, 0x81, 0xF9, 0x7F, 0x96, 0x98, 0x00] (fun s => s.RIP = 0x12a4b5) (cmpR64Imm32Effect 0x12a4b5 1 0x98967f)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm32Effect_footprint 0x12a4b5 1 0x98967f).toInstrSpec (cmp_r64_imm32_effect_step 0x12a4b5 0x48 0xf9 0x98967f (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x12a4bc [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x12a4bc) (movR64R64Effect 0x12a4bc 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a4bc 1 2).toInstrSpec (mov_r64_r64_effect_step 0x12a4bc 0x48 0xd1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a473) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a476) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a479) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a47d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a483) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a486) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a489) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a490) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a493) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a496) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 69), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a499) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a49d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4a3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4a7) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4ab) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 80), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4b1) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4b5) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f17 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 83), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (16, 85), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4bc) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 83), (1, 88), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (16, 85), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4bf) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 90) (jcc_rel8_effect_step 0x12a4bf 7 0xaf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a470 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a470 :=
  Rest.liftedBlock (rest_l12a470 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a470 x hx)

theorem rest_l12a4c1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a4c1 bytes_l12a4c1) (entryMap (live .l12a4c1))
      2 0x12a4c1 bytes_l12a4c1 b_l12a4c1 := by
  have f0 : InstrSpec 0x12a4c1 [0x48, 0x83, 0xFA, 0x09] (fun s => s.RIP = 0x12a4c1) (cmpR64Imm8Effect 0x12a4c1 2 0x9)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x12a4c1 2 0x9).toInstrSpec (cmp_r64_imm8_effect_step 0x12a4c1 0x48 0xfa 0x9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4c5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x12a4c5 6 0x2b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a4c1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a4c1 :=
  Rest.liftedBlock (rest_l12a4c1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a4c1 x hx)

theorem rest_l12a4c7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a4c7 bytes_l12a4c7) (entryMap (live .l12a4c7))
      12 0x12a4c7 bytes_l12a4c7 b_l12a4c7 := by
  have f0 : InstrSpec 0x12a4c7 [0x89, 0xD1] (fun s => s.RIP = 0x12a4c7) (movR32R32Effect 0x12a4c7 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x12a4c7 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x12a4c7 0xd1 (by decide)) pre_rip
  have f1 : InstrSpec 0x12a4c9 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x12a4c9) (shrR32Effect 0x12a4c9 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a4c9 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x12a4c9 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a4cc [0x0F, 0xB7, 0xC9] (fun s => s.RIP = 0x12a4cc) (movzxR32R16Effect 0x12a4cc 3 1 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movzxR32R16Effect_footprint 0x12a4cc 3 1 1).toInstrSpec (movzx_r32_r16_effect_step 0x12a4cc 0xc9 (by decide)) pre_rip
  have f3 : InstrSpec 0x12a4cf [0x69, 0xC9, 0x7B, 0x14, 0x00, 0x00] (fun s => s.RIP = 0x12a4cf) (imulR32R32Imm32Effect 0x12a4cf 6 1 1 0x147b)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (imulR32R32Imm32Effect_footprint 0x12a4cf 6 1 1 0x147b).toInstrSpec (imul_r32_r32_imm32_effect_step 0x12a4cf 0xc9 (by decide) 0x147b) pre_rip
  have f4 : InstrSpec 0x12a4d5 [0xC1, 0xE9, 0x11] (fun s => s.RIP = 0x12a4d5) (shrR32Effect 0x12a4d5 3 1 17)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a4d5 3 1 17).toInstrSpec (shr_r32_imm8_effect_step 0x12a4d5 0xe9 0x11 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12a4d8 [0x44, 0x6B, 0xC9, 0x64] (fun s => s.RIP = 0x12a4d8) (imulR32R32Imm8Effect 0x12a4d8 4 9 1 0x64)
      [.gpr 1] [] [.reg 9, .flags, .rip] :=
    (imulR32R32Imm8Effect_footprint 0x12a4d8 4 9 1 0x64).toInstrSpec (imul_r32_r32_imm8_rex_effect_step 0x12a4d8 0x44 (by decide) 0xc9 (by decide) 0x64) pre_rip
  have f6 : InstrSpec 0x12a4dc [0x44, 0x29, 0xCA] (fun s => s.RIP = 0x12a4dc) (subR32R32Effect 0x12a4dc 3 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (subR32R32Effect_footprint 0x12a4dc 3 2 9).toInstrSpec (sub_r32_r32_rex_effect_step 0x12a4dc 0x44 0xca (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12a4df [0x0F, 0xB7, 0xD2] (fun s => s.RIP = 0x12a4df) (movzxR32R16Effect 0x12a4df 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R16Effect_footprint 0x12a4df 3 2 2).toInstrSpec (movzx_r32_r16_effect_step 0x12a4df 0xd2 (by decide)) pre_rip
  have f8 : InstrSpec 0x12a4e2 [0x0F, 0xB7, 0x14, 0x57] (LoadPre 0x12a4e2 (fun s => AddrMode.addr (.sib 7 (some 2) 1 .none) s (0x12a4e2 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x12a4e2 4 2 (.sib 7 (some 2) 1 .none))
      [.gpr 7, .gpr 2] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x12a4e2 4 2 (.sib 7 (some 2) 1 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x12a4e2 2 (.sib 7 (some 2) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x12a4e6 [0x66, 0x89, 0x54, 0x05, 0xE2] (StorePre 0x12a4e6 5 (fun s => AddrMode.addr (.sib 5 (some 0) 0 (.d8 0xe2)) s (0x12a4e6 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x12a4e6 5 2 (.sib 5 (some 0) 0 (.d8 0xe2)))
      [.gpr 2, .gpr 5, .gpr 0] [] [.rip] :=
    (movM16R16Effect_footprint 0x12a4e6 5 2 (.sib 5 (some 0) 0 (.d8 0xe2))).toInstrSpec (mov_m16_r16_effect_step 0x12a4e6 2 (.sib 5 (some 0) 0 (.d8 0xe2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x12a4eb [0x48, 0x83, 0xC0, 0xFE] (fun s => s.RIP = 0x12a4eb) (addR64Imm8Effect 0x12a4eb 0 0xfe)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12a4eb 0 0xfe).toInstrSpec (add_r64_imm8_effect_step 0x12a4eb 0x48 0xc0 0xfe (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12a4ef [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x12a4ef) (movR64R64Effect 0x12a4ef 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12a4ef 2 1).toInstrSpec (mov_r64_r64_effect_step 0x12a4ef 0x48 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4c9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4cc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4cf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4d5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4d8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4dc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 61), (2, 65), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4df) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 61), (2, 67), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4e2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4e6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4eb) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4ef) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 72), (1, 61), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4f2) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 76) (by decide) rfl

theorem block_l12a4c7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a4c7 :=
  Rest.liftedBlock (rest_l12a4c7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a4c7 x hx)

theorem rest_l12a4f2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a4f2 bytes_l12a4f2) (entryMap (live .l12a4f2))
      2 0x12a4f2 bytes_l12a4f2 b_l12a4f2 := by
  have f0 : InstrSpec 0x12a4f2 [0x4D, 0x85, 0xC0] (fun s => s.RIP = 0x12a4f2) (testR64R64Effect 0x12a4f2 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x12a4f2 8 8).toInstrSpec (test_r64_r64_effect_step 0x12a4f2 0x4d 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4f5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12a4f5 4 0x5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a4f2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a4f2 :=
  Rest.liftedBlock (rest_l12a4f2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a4f2 x hx)

theorem rest_l12a4f7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a4f7 bytes_l12a4f7) (entryMap (live .l12a4f7))
      2 0x12a4f7 bytes_l12a4f7 b_l12a4f7 := by
  have f0 : InstrSpec 0x12a4f7 [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x12a4f7) (testR64R64Effect 0x12a4f7 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x12a4f7 2 2).toInstrSpec (test_r64_r64_effect_step 0x12a4f7 0x48 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4fa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12a4fa 4 0xc) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a4f7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a4f7 :=
  Rest.liftedBlock (rest_l12a4f7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a4f7 x hx)

theorem rest_l12a4fc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a4fc bytes_l12a4fc) (entryMap (live .l12a4fc))
      3 0x12a4fc bytes_l12a4fc b_l12a4fc := by
  have f0 : InstrSpec 0x12a4fc [0x0F, 0xB6, 0x4C, 0x57, 0x01] (LoadPre 0x12a4fc (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x1)) s (0x12a4fc + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x12a4fc 5 1 (.sib 7 (some 2) 1 (.d8 0x1)))
      [.gpr 7, .gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x12a4fc 5 1 (.sib 7 (some 2) 1 (.d8 0x1))).toInstrSpec (movzx_r32_m8_effect_step 0x12a4fc 1 (.sib 7 (some 2) 1 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12a501 [0x88, 0x4C, 0x05, 0xE3] (StorePre 0x12a501 4 (fun s => AddrMode.addr (.sib 5 (some 0) 0 (.d8 0xe3)) s (0x12a501 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x12a501 4 1 (.sib 5 (some 0) 0 (.d8 0xe3)))
      [.gpr 1, .gpr 5, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x12a501 4 1 (.sib 5 (some 0) 0 (.d8 0xe3))).toInstrSpec (mov_m8_r8_effect_step 0x12a501 1 (by decide) (.sib 5 (some 0) 0 (.d8 0xe3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12a505 [0x48, 0xFF, 0xC8] (fun s => s.RIP = 0x12a505) (decR64Effect 0x12a505 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (decR64Effect_footprint 0x12a505 0).toInstrSpec (dec_r64_effect_step 0x12a505 0x48 0xc8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a501) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a505) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a508) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l12a4fc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a4fc :=
  Rest.liftedBlock (rest_l12a4fc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a4fc x hx)

theorem rest_l12a508 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a508 bytes_l12a508) (entryMap (live .l12a508))
      9 0x12a508 bytes_l12a508 b_l12a508 := by
  have f0 : InstrSpec 0x12a508 [0x41, 0xB9, 0x14, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a508) (movR32Imm32Effect 0x12a508 6 9 0x14)
      [] [] [.reg 9, .rip] :=
    (movR32Imm32Effect_footprint 0x12a508 6 9 0x14).toInstrSpec (mov_r32_imm32_rex_effect_step 0x12a508 0x41 0xb9 (by decide) (by decide) 0x14) pre_rip
  have f1 : InstrSpec 0x12a50e [0x49, 0x29, 0xC1] (fun s => s.RIP = 0x12a50e) (subR64R64Effect 0x12a50e 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x12a50e 9 0).toInstrSpec (sub_r64_r64_effect_step 0x12a50e 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a511 [0x4C, 0x8D, 0x04, 0x28] (fun s => s.RIP = 0x12a511) (leaR64Effect 0x12a511 8 (.sib 0 (some 5) 0 .none))
      [.gpr 0, .gpr 5] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x12a511 8 (.sib 0 (some 5) 0 .none)).toInstrSpec (lea_r64_effect_step 0x12a511 0x4c (by decide) 0 (.sib 0 (some 5) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12a515 [0x49, 0x83, 0xC0, 0xE4] (fun s => s.RIP = 0x12a515) (addR64Imm8Effect 0x12a515 8 0xe4)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12a515 8 0xe4).toInstrSpec (add_r64_imm8_effect_step 0x12a515 0x49 0xc0 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a519 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a519) (movR32Imm32Effect 0x12a519 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x12a519 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x12a519 0xba (by decide) 0x1) pre_rip
  have f5 : InstrSpec 0x12a51e [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x12a51e) (movR64R64Effect 0x12a51e 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12a51e 7 6).toInstrSpec (mov_r64_r64_effect_step 0x12a51e 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12a521 [0xBE, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a521) (movR32Imm32Effect 0x12a521 5 6 0x1)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x12a521 5 6 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x12a521 0xbe (by decide) 0x1) pre_rip
  have f7 : InstrSpec 0x12a526 [0x31, 0xC9] (fun s => s.RIP = 0x12a526) (xorR32R32Effect 0x12a526 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12a526 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x12a526 0xc9 (by decide)) pre_rip
  have f8 : InstrSpec 0x12a528 [0xFF, 0x15, 0xBA, 0x98, 0x0D, 0x00] (GoesTo (CallMemPre 0x12a528 (.rip 0xd98ba)) (callEffect (callMemPtr 0x12a528 (.rip 0xd98ba)) (0x12a528 + BitVec.ofNat 64 (callMemLen (.rip 0xd98ba)))) 0x128b20) (callEffect (callMemPtr 0x12a528 (.rip 0xd98ba)) (0x12a528 + BitVec.ofNat 64 (callMemLen (.rip 0xd98ba))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x12a528 (.rip 0xd98ba)).toInstrSpec (call_m64_effect_step 0x12a528 (.rip 0xd98ba) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x128b20
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a50e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a511) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 57), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a515) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 59), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a519) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (8, 59), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a51e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (8, 59), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a521) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a526) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 61), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a528) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 67), (2, 61), (3, 3), (4, 69), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b20) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l12a508 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a508 :=
  Rest.liftedBlock (rest_l12a508 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a508 x hx)

theorem rest_l12a52e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a52e bytes_l12a52e) (entryMap (live .l12a52e))
      4 0x12a52e bytes_l12a52e b_l12a52e := by
  have f0 : InstrSpec 0x12a52e [0x48, 0x83, 0xC4, 0x18] (fun s => s.RIP = 0x12a52e) (addR64Imm8Effect 0x12a52e 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12a52e 4 0x18).toInstrSpec (add_r64_imm8_effect_step 0x12a52e 0x48 0xc4 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a532 [0x5B] (PopPre 0x12a532) (popR64Effect 0x12a532 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12a532 1 3).toInstrSpec (pop_r64_effect_step 0x12a532 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x12a533 [0x5D] (PopPre 0x12a533) (popR64Effect 0x12a533 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12a533 1 5).toInstrSpec (pop_r64_effect_step 0x12a533 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x12a534 [0xC3] (RetPre 0x12a534) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12a534).toInstrSpec (ret_effect_step 0x12a534) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a532) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a533) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (5, 58), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a534) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (5, 58), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f3 (by decide) rfl rfl rfl (by decide)

theorem block_l12a52e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a52e :=
  Rest.liftedBlock (rest_l12a52e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a52e x hx)

theorem rest_l12a820 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a820 bytes_l12a820) (entryMap (live .l12a820))
      16 0x12a820 bytes_l12a820 b_l12a820 := by
  have f0 : InstrSpec 0x12a820 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x12a820) (movR64R64Effect 0x12a820 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12a820 0 7).toInstrSpec (mov_r64_r64_effect_step 0x12a820 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a823 [0x41, 0x89, 0xC0] (fun s => s.RIP = 0x12a823) (movR32R32Effect 0x12a823 3 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x12a823 3 8 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x12a823 0x41 0xc0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a826 [0x41, 0xF7, 0xD8] (fun s => s.RIP = 0x12a826) (negR32Effect 0x12a826 3 8)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (negR32Effect_footprint 0x12a826 3 8).toInstrSpec (neg_r32_rex_effect_step 0x12a826 0x41 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12a829 [0x41, 0x83, 0xE0, 0x07] (fun s => s.RIP = 0x12a829) (andR32Imm8Effect 0x12a829 4 8 0x7)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x12a829 4 8 0x7).toInstrSpec (and_r32_imm8_rex_effect_step 0x12a829 0x41 0xe0 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a82d [0x4C, 0x39, 0xC2] (fun s => s.RIP = 0x12a82d) (cmpR64R64Effect 0x12a82d 2 8)
      [.gpr 2, .gpr 8] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12a82d 2 8).toInstrSpec (cmp_r64_r64_effect_step 0x12a82d 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12a830 [0x4C, 0x0F, 0x42, 0xC2] (fun s => s.RIP = 0x12a830) (atFlags (condHolds 2) (cmovR64R64Effect 0x12a830 4 8 2))
      [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .rip] :=
    (cmovR64R64Effect_footprint 0x12a830 4 8 2 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x12a830 2 0x4c (by decide) 0xc2 (by decide) c)) pre_rip
  have f6 : InstrSpec 0x12a834 [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x12a834) (movR64R64Effect 0x12a834 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a834 1 8).toInstrSpec (mov_r64_r64_effect_step 0x12a834 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12a837 [0xF3, 0xA4] (RepPre 0x12a837 (RepMovsbPre 0x12a837)) (repMovsbEffect 0x12a837)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsbEffect_footprint 0x12a837).toInstrSpecOfRuns (rep_movsb_runs hstride 0x12a837) (RepMovsOk.of_stateOf RepMovsbPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f8 : InstrSpec 0x12a839 [0x4C, 0x29, 0xC2] (fun s => s.RIP = 0x12a839) (subR64R64Effect 0x12a839 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x12a839 2 8).toInstrSpec (sub_r64_r64_effect_step 0x12a839 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x12a83c [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x12a83c) (movR64R64Effect 0x12a83c 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a83c 1 2).toInstrSpec (mov_r64_r64_effect_step 0x12a83c 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x12a83f [0x48, 0xC1, 0xE9, 0x03] (fun s => s.RIP = 0x12a83f) (shrR64Effect 0x12a83f 4 1 3)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x12a83f 4 1 3).toInstrSpec (shr_r64_imm8_effect_step 0x12a83f 0x48 0xe9 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12a843 [0xF3, 0x48, 0xA5] (RepPre 0x12a843 (RepMovsqPre 0x12a843)) (repMovsqEffect 0x12a843)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x12a843).toInstrSpecOfRuns (rep_movsq_runs hstride 0x12a843 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f12 : InstrSpec 0x12a846 [0x83, 0xE2, 0x07] (fun s => s.RIP = 0x12a846) (andR32Imm8Effect 0x12a846 3 2 0x7)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x12a846 3 2 0x7).toInstrSpec (and_r32_imm8_effect_step 0x12a846 0xe2 0x7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x12a849 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x12a849) (movR64R64Effect 0x12a849 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a849 1 2).toInstrSpec (mov_r64_r64_effect_step 0x12a849 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x12a84c [0xF3, 0xA4] (RepPre 0x12a84c (RepMovsbPre 0x12a84c)) (repMovsbEffect 0x12a84c)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsbEffect_footprint 0x12a84c).toInstrSpecOfRuns (rep_movsb_runs hstride 0x12a84c) (RepMovsOk.of_stateOf RepMovsbPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f15 : InstrSpec 0x12a84e [0xC3] (RetPre 0x12a84e) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12a84e).toInstrSpec (ret_effect_step 0x12a84e) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a823) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a826) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a829) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a82d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a830) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a834) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a837) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a839) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (2, 70), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a83c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 72), (2, 70), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a83f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 74), (2, 70), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a843) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(0, 53), (2, 70), (3, 3), (4, 4), (5, 5), (6, 76), (7, 77), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a846) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 53), (2, 79), (3, 3), (4, 4), (5, 5), (6, 76), (7, 77), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a849) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 53), (1, 81), (2, 79), (3, 3), (4, 4), (5, 5), (6, 76), (7, 77), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a84c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 84) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 85) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 86) (ρ' := [(0, 53), (1, 85), (2, 79), (3, 3), (4, 4), (5, 5), (6, 83), (7, 84), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a84e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f15 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 88) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 89) (ρ' := [(0, 53), (1, 85), (2, 79), (3, 3), (4, 88), (5, 5), (6, 83), (7, 84), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f15 (by decide) rfl rfl rfl (by decide)

theorem block_l12a820 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a820 :=
  Rest.liftedBlock (rest_l12a820 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a820 x hx)

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

theorem_by block_l100a20_eval :
    program.runBlock (dialect code) ⟨.l100a20, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102450_eval :
    program.runBlock (dialect code) ⟨.l102450, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10245b_eval :
    program.runBlock (dialect code) ⟨.l10245b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102468_eval :
    program.runBlock (dialect code) ⟨.l102468, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10246f_eval :
    program.runBlock (dialect code) ⟨.l10246f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1024d0_eval :
    program.runBlock (dialect code) ⟨.l1024d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1024d6_eval :
    program.runBlock (dialect code) ⟨.l1024d6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1024df_eval :
    program.runBlock (dialect code) ⟨.l1024df, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1024ee_eval :
    program.runBlock (dialect code) ⟨.l1024ee, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1024fb_eval :
    program.runBlock (dialect code) ⟨.l1024fb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1024fd_eval :
    program.runBlock (dialect code) ⟨.l1024fd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127d50_eval :
    program.runBlock (dialect code) ⟨.l127d50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127f50_eval :
    program.runBlock (dialect code) ⟨.l127f50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127f55_eval :
    program.runBlock (dialect code) ⟨.l127f55, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127f5a_eval :
    program.runBlock (dialect code) ⟨.l127f5a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127f70_eval :
    program.runBlock (dialect code) ⟨.l127f70, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127f8a_eval :
    program.runBlock (dialect code) ⟨.l127f8a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127f9a_eval :
    program.runBlock (dialect code) ⟨.l127f9a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127fa9_eval :
    program.runBlock (dialect code) ⟨.l127fa9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1295f2_eval :
    program.runBlock (dialect code) ⟨.l1295f2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12962f_eval :
    program.runBlock (dialect code) ⟨.l12962f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12965d_eval :
    program.runBlock (dialect code) ⟨.l12965d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1296a9_eval :
    program.runBlock (dialect code) ⟨.l1296a9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1296eb_eval :
    program.runBlock (dialect code) ⟨.l1296eb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12974b_eval :
    program.runBlock (dialect code) ⟨.l12974b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129762_eval :
    program.runBlock (dialect code) ⟨.l129762, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129770_eval :
    program.runBlock (dialect code) ⟨.l129770, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12979c_eval :
    program.runBlock (dialect code) ⟨.l12979c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c30_eval :
    program.runBlock (dialect code) ⟨.l129c30, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c4c_eval :
    program.runBlock (dialect code) ⟨.l129c4c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c56_eval :
    program.runBlock (dialect code) ⟨.l129c56, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c5e_eval :
    program.runBlock (dialect code) ⟨.l129c5e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c63_eval :
    program.runBlock (dialect code) ⟨.l129c63, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c7b_eval :
    program.runBlock (dialect code) ⟨.l129c7b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c7d_eval :
    program.runBlock (dialect code) ⟨.l129c7d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a050_eval :
    program.runBlock (dialect code) ⟨.l12a050, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a070_eval :
    program.runBlock (dialect code) ⟨.l12a070, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a100_eval :
    program.runBlock (dialect code) ⟨.l12a100, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a430_eval :
    program.runBlock (dialect code) ⟨.l12a430, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a454_eval :
    program.runBlock (dialect code) ⟨.l12a454, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a470_eval :
    program.runBlock (dialect code) ⟨.l12a470, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a4c1_eval :
    program.runBlock (dialect code) ⟨.l12a4c1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a4c7_eval :
    program.runBlock (dialect code) ⟨.l12a4c7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a4f2_eval :
    program.runBlock (dialect code) ⟨.l12a4f2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a4f7_eval :
    program.runBlock (dialect code) ⟨.l12a4f7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a4fc_eval :
    program.runBlock (dialect code) ⟨.l12a4fc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a508_eval :
    program.runBlock (dialect code) ⟨.l12a508, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a52e_eval :
    program.runBlock (dialect code) ⟨.l12a52e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a820_eval :
    program.runBlock (dialect code) ⟨.l12a820, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.LIR
