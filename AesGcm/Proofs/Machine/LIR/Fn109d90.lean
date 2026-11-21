import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l109d90 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109d90 bytes_l109d90) (entryMap (live .l109d90))
      5 0x109d90 bytes_l109d90 b_l109d90 := by
  have f0 : InstrSpec 0x109d90 [0x55] (PushPre 0x109d90 1) (pushR64Effect 0x109d90 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109d90 1 5).toInstrSpec (push_r64_effect_step 0x109d90 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x109d91 [0x53] (PushPre 0x109d91 1) (pushR64Effect 0x109d91 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109d91 1 3).toInstrSpec (push_r64_effect_step 0x109d91 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x109d92 [0x50] (PushPre 0x109d92 1) (pushR64Effect 0x109d92 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109d92 1 0).toInstrSpec (push_r64_effect_step 0x109d92 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x109d93 [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x109d93) (testR64R64Effect 0x109d93 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x109d93 2 2).toInstrSpec (test_r64_r64_effect_step 0x109d93 0x48 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d91) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d92) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d93) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d96) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel32_effect_step 0x109d96 4 0x1a5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l109d90 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109d90 :=
  Rest.liftedBlock (rest_l109d90 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109d90 x hx)

theorem rest_l109d9c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109d9c bytes_l109d9c) (entryMap (live .l109d9c))
      2 0x109d9c bytes_l109d9c b_l109d9c := by
  have f0 : InstrSpec 0x109d9c [0x48, 0x83, 0xFA, 0x01] (fun s => s.RIP = 0x109d9c) (cmpR64Imm8Effect 0x109d9c 2 0x1)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x109d9c 2 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x109d9c 0x48 0xfa 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109da0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x109da0 4 0x1ab) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l109d9c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109d9c :=
  Rest.liftedBlock (rest_l109d9c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109d9c x hx)

theorem rest_l109da6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109da6 bytes_l109da6) (entryMap (live .l109da6))
      2 0x109da6 bytes_l109da6 b_l109da6 := by
  have f0 : InstrSpec 0x109da6 [0x48, 0x83, 0xFA, 0x02] (fun s => s.RIP = 0x109da6) (cmpR64Imm8Effect 0x109da6 2 0x2)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x109da6 2 0x2).toInstrSpec (cmp_r64_imm8_effect_step 0x109da6 0x48 0xfa 0x2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109daa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x109daa 6 0x1b7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l109da6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109da6 :=
  Rest.liftedBlock (rest_l109da6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109da6 x hx)

theorem rest_l109db0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109db0 bytes_l109db0) (entryMap (live .l109db0))
      2 0x109db0 bytes_l109db0 b_l109db0 := by
  have f0 : InstrSpec 0x109db0 [0x48, 0x83, 0xFA, 0x03] (fun s => s.RIP = 0x109db0) (cmpR64Imm8Effect 0x109db0 2 0x3)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x109db0 2 0x3).toInstrSpec (cmp_r64_imm8_effect_step 0x109db0 0x48 0xfa 0x3 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109db4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x109db4 4 0x1c3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l109db0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109db0 :=
  Rest.liftedBlock (rest_l109db0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109db0 x hx)

theorem rest_l109dba [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109dba bytes_l109dba) (entryMap (live .l109dba))
      2 0x109dba bytes_l109dba b_l109dba := by
  have f0 : InstrSpec 0x109dba [0x48, 0x83, 0xFA, 0x04] (fun s => s.RIP = 0x109dba) (cmpR64Imm8Effect 0x109dba 2 0x4)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x109dba 2 0x4).toInstrSpec (cmp_r64_imm8_effect_step 0x109dba 0x48 0xfa 0x4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109dbe) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x109dbe 6 0x1cf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l109dba [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109dba :=
  Rest.liftedBlock (rest_l109dba code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109dba x hx)

theorem rest_l109dc4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109dc4 bytes_l109dc4) (entryMap (live .l109dc4))
      2 0x109dc4 bytes_l109dc4 b_l109dc4 := by
  have f0 : InstrSpec 0x109dc4 [0x48, 0x83, 0xFA, 0x05] (fun s => s.RIP = 0x109dc4) (cmpR64Imm8Effect 0x109dc4 2 0x5)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x109dc4 2 0x5).toInstrSpec (cmp_r64_imm8_effect_step 0x109dc4 0x48 0xfa 0x5 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109dc8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x109dc8 4 0x1db) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l109dc4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109dc4 :=
  Rest.liftedBlock (rest_l109dc4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109dc4 x hx)

theorem rest_l109dce [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109dce bytes_l109dce) (entryMap (live .l109dce))
      2 0x109dce bytes_l109dce b_l109dce := by
  have f0 : InstrSpec 0x109dce [0x48, 0x83, 0xFA, 0x06] (fun s => s.RIP = 0x109dce) (cmpR64Imm8Effect 0x109dce 2 0x6)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x109dce 2 0x6).toInstrSpec (cmp_r64_imm8_effect_step 0x109dce 0x48 0xfa 0x6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109dd2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x109dd2 6 0x1e7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l109dce [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109dce :=
  Rest.liftedBlock (rest_l109dce code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109dce x hx)

theorem rest_l109dd8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109dd8 bytes_l109dd8) (entryMap (live .l109dd8))
      2 0x109dd8 bytes_l109dd8 b_l109dd8 := by
  have f0 : InstrSpec 0x109dd8 [0x48, 0x83, 0xFA, 0x07] (fun s => s.RIP = 0x109dd8) (cmpR64Imm8Effect 0x109dd8 2 0x7)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x109dd8 2 0x7).toInstrSpec (cmp_r64_imm8_effect_step 0x109dd8 0x48 0xfa 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ddc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x109ddc 4 0x1f3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l109dd8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109dd8 :=
  Rest.liftedBlock (rest_l109dd8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109dd8 x hx)

theorem rest_l109de2_5 [Bindings] (code : CodeMap) :
    Rest (n := 241) code lifted (codeRange 0x109de2 bytes_l109de2) [(0, 239), (1, 211), (2, 133), (3, 225), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      14 0x109f1b bytes_l109de2_5 b_l109de2_5 := by
  have f100 : InstrSpec 0x109f1b [0x25, 0x0F, 0x0F, 0x00, 0x00] (fun s => s.RIP = 0x109f1b) (andEaxImm32Effect 0x109f1b 0xf0f)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x109f1b 0xf0f).toInstrSpec (and_eax_imm32_effect_step 0x109f1b 0xf0f) pre_rip
  have f101 : InstrSpec 0x109f20 [0x31, 0xC5] (fun s => s.RIP = 0x109f20) (xorR32R32Effect 0x109f20 2 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109f20 2 5 0).toInstrSpec (xor_r32_r32_effect_step 0x109f20 0xc5 (by decide)) pre_rip
  have f102 : InstrSpec 0x109f22 [0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x109f22) (shlR32Effect 0x109f22 3 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x109f22 3 0 4).toInstrSpec (shl_r32_imm8_effect_step 0x109f22 0xe0 0x4 (by decide) (by decide)) pre_rip
  have f103 : InstrSpec 0x109f25 [0x44, 0x31, 0xD0] (fun s => s.RIP = 0x109f25) (xorR32R32Effect 0x109f25 3 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109f25 3 0 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x109f25 0x44 0xd0 (by decide) (by decide)) pre_rip
  have f104 : InstrSpec 0x109f28 [0x88, 0x47, 0x0C] (StorePre 0x109f28 3 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x109f28 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109f28 3 0 (.base 7 (.d8 0xc)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x109f28 3 0 (.base 7 (.d8 0xc))).toInstrSpec (mov_m8_r8_effect_step 0x109f28 0 (by decide) (.base 7 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f105 : InstrSpec 0x109f2b [0x40, 0x88, 0x6F, 0x0D] (StorePre 0x109f2b 4 (fun s => AddrMode.addr (.base 7 (.d8 0xd)) s (0x109f2b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109f2b 4 5 (.base 7 (.d8 0xd)))
      [.gpr 5, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x109f2b 4 5 (.base 7 (.d8 0xd))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109f2b 0x40 (by decide) 5 (.base 7 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f106 : InstrSpec 0x109f2f [0x89, 0xE9] (fun s => s.RIP = 0x109f2f) (movR32R32Effect 0x109f2f 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x109f2f 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x109f2f 0xe9 (by decide)) pre_rip
  have f107 : InstrSpec 0x109f31 [0x88, 0x67, 0x0E] (StorePre 0x109f31 3 (fun s => AddrMode.addr (.base 7 (.d8 0xe)) s (0x109f31 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x109f31 3 4 (.base 7 (.d8 0xe)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x109f31 3 4 (.base 7 (.d8 0xe))).toInstrSpec (mov_m8_r8_norex_effect_step 0x109f31 4 (.base 7 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f108 : InstrSpec 0x109f34 [0x88, 0x6F, 0x0F] (StorePre 0x109f34 3 (fun s => AddrMode.addr (.base 7 (.d8 0xf)) s (0x109f34 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x109f34 3 5 (.base 7 (.d8 0xf)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x109f34 3 5 (.base 7 (.d8 0xf))).toInstrSpec (mov_m8_r8_norex_effect_step 0x109f34 5 (.base 7 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f109 : InstrSpec 0x109f37 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x109f37) (movR64R64Effect 0x109f37 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109f37 0 7).toInstrSpec (mov_r64_r64_effect_step 0x109f37 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f110 : InstrSpec 0x109f3a [0x48, 0x83, 0xC4, 0x08] (fun s => s.RIP = 0x109f3a) (addR64Imm8Effect 0x109f3a 4 0x8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x109f3a 4 0x8).toInstrSpec (add_r64_imm8_effect_step 0x109f3a 0x48 0xc4 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f111 : InstrSpec 0x109f3e [0x5B] (PopPre 0x109f3e) (popR64Effect 0x109f3e 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109f3e 1 3).toInstrSpec (pop_r64_effect_step 0x109f3e 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f112 : InstrSpec 0x109f3f [0x5D] (PopPre 0x109f3f) (popR64Effect 0x109f3f 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109f3f 1 5).toInstrSpec (pop_r64_effect_step 0x109f3f 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f113 : InstrSpec 0x109f40 [0xC3] (RetPre 0x109f40) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x109f40).toInstrSpec (ret_effect_step 0x109f40) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 241) (RestInside.out (n := 241) f100 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 242) (ρ' := [(0, 241), (1, 211), (2, 133), (3, 225), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f20) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 243) (RestInside.out (n := 243) f101 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 244) (ρ' := [(0, 241), (1, 211), (2, 133), (3, 225), (4, 4), (5, 243), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f22) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 245) (RestInside.out (n := 245) f102 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 246) (ρ' := [(0, 245), (1, 211), (2, 133), (3, 225), (4, 4), (5, 243), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f25) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f103 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 248) (ρ' := [(0, 247), (1, 211), (2, 133), (3, 225), (4, 4), (5, 243), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f28) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 249) (RestInside.exec (n := 249) (ρ' := [(0, 247), (1, 211), (2, 133), (3, 225), (4, 4), (5, 243), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f2b) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 250) (RestInside.exec (n := 250) (ρ' := [(0, 247), (1, 211), (2, 133), (3, 225), (4, 4), (5, 243), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f2f) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 251) (RestInside.out (n := 251) f106 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 252) (ρ' := [(0, 247), (1, 251), (2, 133), (3, 225), (4, 4), (5, 243), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f31) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 253) (RestInside.exec (n := 253) (ρ' := [(0, 247), (1, 251), (2, 133), (3, 225), (4, 4), (5, 243), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f34) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 254) (RestInside.exec (n := 254) (ρ' := [(0, 247), (1, 251), (2, 133), (3, 225), (4, 4), (5, 243), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f37) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 255) (RestInside.out (n := 255) f109 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 256) (ρ' := [(0, 255), (1, 251), (2, 133), (3, 225), (4, 4), (5, 243), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f3a) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 257) (RestInside.out (n := 257) f110 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 258) (ρ' := [(0, 255), (1, 251), (2, 133), (3, 225), (4, 257), (5, 243), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f3e) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f111 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 260) f111 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 261) (ρ' := [(0, 255), (1, 251), (2, 133), (3, 259), (4, 260), (5, 243), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f3f) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 262) (RestInside.out (n := 262) f112 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 263) f112 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 264) (ρ' := [(0, 255), (1, 251), (2, 133), (3, 259), (4, 263), (5, 262), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f40) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 265) (RestInside.out (n := 265) f113 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 266) f113 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 267) (ρ' := [(0, 255), (1, 251), (2, 133), (3, 259), (4, 266), (5, 262), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f113 (by decide) rfl rfl rfl (by decide)

theorem rest_l109de2_4 [Bindings] (code : CodeMap) :
    Rest (n := 209) code lifted (codeRange 0x109de2 bytes_l109de2) [(0, 207), (1, 205), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      34 0x109ee3 bytes_l109de2_4 b_l109de2_4 := by
  have f80 : InstrSpec 0x109ee3 [0xC1, 0xE1, 0x04] (fun s => s.RIP = 0x109ee3) (shlR32Effect 0x109ee3 3 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x109ee3 3 1 4).toInstrSpec (shl_r32_imm8_effect_step 0x109ee3 0xe1 0x4 (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x109ee6 [0x31, 0xF1] (fun s => s.RIP = 0x109ee6) (xorR32R32Effect 0x109ee6 2 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109ee6 2 1 6).toInstrSpec (xor_r32_r32_effect_step 0x109ee6 0xf1 (by decide)) pre_rip
  have f82 : InstrSpec 0x109ee8 [0x88, 0x4F, 0x04] (StorePre 0x109ee8 3 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x109ee8 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109ee8 3 1 (.base 7 (.d8 0x4)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x109ee8 3 1 (.base 7 (.d8 0x4))).toInstrSpec (mov_m8_r8_effect_step 0x109ee8 1 (by decide) (.base 7 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f83 : InstrSpec 0x109eeb [0x88, 0x47, 0x05] (StorePre 0x109eeb 3 (fun s => AddrMode.addr (.base 7 (.d8 0x5)) s (0x109eeb + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109eeb 3 0 (.base 7 (.d8 0x5)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x109eeb 3 0 (.base 7 (.d8 0x5))).toInstrSpec (mov_m8_r8_effect_step 0x109eeb 0 (by decide) (.base 7 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f84 : InstrSpec 0x109eee [0x88, 0x6F, 0x06] (StorePre 0x109eee 3 (fun s => AddrMode.addr (.base 7 (.d8 0x6)) s (0x109eee + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x109eee 3 5 (.base 7 (.d8 0x6)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x109eee 3 5 (.base 7 (.d8 0x6))).toInstrSpec (mov_m8_r8_norex_effect_step 0x109eee 5 (.base 7 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f85 : InstrSpec 0x109ef1 [0x88, 0x67, 0x07] (StorePre 0x109ef1 3 (fun s => AddrMode.addr (.base 7 (.d8 0x7)) s (0x109ef1 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x109ef1 3 4 (.base 7 (.d8 0x7)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x109ef1 3 4 (.base 7 (.d8 0x7))).toInstrSpec (mov_m8_r8_norex_effect_step 0x109ef1 4 (.base 7 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f86 : InstrSpec 0x109ef4 [0x89, 0xD0] (fun s => s.RIP = 0x109ef4) (movR32R32Effect 0x109ef4 2 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x109ef4 2 0 2).toInstrSpec (mov_r32_r32_effect_step 0x109ef4 0xd0 (by decide)) pre_rip
  have f87 : InstrSpec 0x109ef6 [0xC1, 0xE8, 0x04] (fun s => s.RIP = 0x109ef6) (shrR32Effect 0x109ef6 3 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x109ef6 3 0 4).toInstrSpec (shr_r32_imm8_effect_step 0x109ef6 0xe8 0x4 (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x109ef9 [0x31, 0xD8] (fun s => s.RIP = 0x109ef9) (xorR32R32Effect 0x109ef9 2 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109ef9 2 0 3).toInstrSpec (xor_r32_r32_effect_step 0x109ef9 0xd8 (by decide)) pre_rip
  have f89 : InstrSpec 0x109efb [0x25, 0x0F, 0x0F, 0x00, 0x00] (fun s => s.RIP = 0x109efb) (andEaxImm32Effect 0x109efb 0xf0f)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x109efb 0xf0f).toInstrSpec (and_eax_imm32_effect_step 0x109efb 0xf0f) pre_rip
  have f90 : InstrSpec 0x109f00 [0x31, 0xC3] (fun s => s.RIP = 0x109f00) (xorR32R32Effect 0x109f00 2 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109f00 2 3 0).toInstrSpec (xor_r32_r32_effect_step 0x109f00 0xc3 (by decide)) pre_rip
  have f91 : InstrSpec 0x109f02 [0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x109f02) (shlR32Effect 0x109f02 3 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x109f02 3 0 4).toInstrSpec (shl_r32_imm8_effect_step 0x109f02 0xe0 0x4 (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x109f05 [0x31, 0xD0] (fun s => s.RIP = 0x109f05) (xorR32R32Effect 0x109f05 2 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109f05 2 0 2).toInstrSpec (xor_r32_r32_effect_step 0x109f05 0xd0 (by decide)) pre_rip
  have f93 : InstrSpec 0x109f07 [0x88, 0x47, 0x08] (StorePre 0x109f07 3 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x109f07 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109f07 3 0 (.base 7 (.d8 0x8)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x109f07 3 0 (.base 7 (.d8 0x8))).toInstrSpec (mov_m8_r8_effect_step 0x109f07 0 (by decide) (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f94 : InstrSpec 0x109f0a [0x88, 0x5F, 0x09] (StorePre 0x109f0a 3 (fun s => AddrMode.addr (.base 7 (.d8 0x9)) s (0x109f0a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109f0a 3 3 (.base 7 (.d8 0x9)))
      [.gpr 3, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x109f0a 3 3 (.base 7 (.d8 0x9))).toInstrSpec (mov_m8_r8_effect_step 0x109f0a 3 (by decide) (.base 7 (.d8 0x9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f95 : InstrSpec 0x109f0d [0x88, 0x67, 0x0A] (StorePre 0x109f0d 3 (fun s => AddrMode.addr (.base 7 (.d8 0xa)) s (0x109f0d + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x109f0d 3 4 (.base 7 (.d8 0xa)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x109f0d 3 4 (.base 7 (.d8 0xa))).toInstrSpec (mov_m8_r8_norex_effect_step 0x109f0d 4 (.base 7 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f96 : InstrSpec 0x109f10 [0x88, 0x7F, 0x0B] (StorePre 0x109f10 3 (fun s => AddrMode.addr (.base 7 (.d8 0xb)) s (0x109f10 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x109f10 3 7 (.base 7 (.d8 0xb)))
      [.gpr 3, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x109f10 3 7 (.base 7 (.d8 0xb))).toInstrSpec (mov_m8_r8_norex_effect_step 0x109f10 7 (.base 7 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f97 : InstrSpec 0x109f13 [0x44, 0x89, 0xD0] (fun s => s.RIP = 0x109f13) (movR32R32Effect 0x109f13 3 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x109f13 3 0 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x109f13 0x44 0xd0 (by decide) (by decide)) pre_rip
  have f98 : InstrSpec 0x109f16 [0xC1, 0xE8, 0x04] (fun s => s.RIP = 0x109f16) (shrR32Effect 0x109f16 3 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x109f16 3 0 4).toInstrSpec (shr_r32_imm8_effect_step 0x109f16 0xe8 0x4 (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x109f19 [0x31, 0xE8] (fun s => s.RIP = 0x109f19) (xorR32R32Effect 0x109f19 2 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109f19 2 0 5).toInstrSpec (xor_r32_r32_effect_step 0x109f19 0xe8 (by decide)) pre_rip
  refine Rest.ofInside (n := 209) (RestInside.out (n := 209) f80 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 210) (ρ' := [(0, 207), (1, 209), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ee6) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 211) (RestInside.out (n := 211) f81 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 212) (ρ' := [(0, 207), (1, 211), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ee8) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 213) (RestInside.exec (n := 213) (ρ' := [(0, 207), (1, 211), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eeb) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 214) (RestInside.exec (n := 214) (ρ' := [(0, 207), (1, 211), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eee) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 215) (RestInside.exec (n := 215) (ρ' := [(0, 207), (1, 211), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ef1) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 216) (RestInside.exec (n := 216) (ρ' := [(0, 207), (1, 211), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ef4) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 217) (RestInside.out (n := 217) f86 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 218) (ρ' := [(0, 217), (1, 211), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ef6) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f87 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 219), (1, 211), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ef9) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f88 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 221), (1, 211), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109efb) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f89 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(0, 223), (1, 211), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f00) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f90 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(0, 223), (1, 211), (2, 133), (3, 225), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f02) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f91 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 227), (1, 211), (2, 133), (3, 225), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f05) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.out (n := 229) f92 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 230) (ρ' := [(0, 229), (1, 211), (2, 133), (3, 225), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f07) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.exec (n := 231) (ρ' := [(0, 229), (1, 211), (2, 133), (3, 225), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f0a) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 232) (RestInside.exec (n := 232) (ρ' := [(0, 229), (1, 211), (2, 133), (3, 225), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f0d) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 233) (RestInside.exec (n := 233) (ρ' := [(0, 229), (1, 211), (2, 133), (3, 225), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f10) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 234) (RestInside.exec (n := 234) (ρ' := [(0, 229), (1, 211), (2, 133), (3, 225), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f13) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 235) (RestInside.out (n := 235) f97 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 236) (ρ' := [(0, 235), (1, 211), (2, 133), (3, 225), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f16) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 237) (RestInside.out (n := 237) f98 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 238) (ρ' := [(0, 237), (1, 211), (2, 133), (3, 225), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f19) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 239) (RestInside.out (n := 239) f99 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 240) (ρ' := [(0, 239), (1, 211), (2, 133), (3, 225), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f1b) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109de2_5 code

theorem rest_l109de2_3 [Bindings] (code : CodeMap) :
    Rest (n := 170) code lifted (codeRange 0x109de2 bytes_l109de2) [(0, 165), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      54 0x109ea4 bytes_l109de2_3 b_l109de2_3 := by
  have f60 : InstrSpec 0x109ea4 [0x44, 0x89, 0xCE] (fun s => s.RIP = 0x109ea4) (movR32R32Effect 0x109ea4 3 6 9)
      [.gpr 9] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x109ea4 3 6 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x109ea4 0x44 0xce (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x109ea7 [0xC1, 0xEE, 0x02] (fun s => s.RIP = 0x109ea7) (shrR32Effect 0x109ea7 3 6 2)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x109ea7 3 6 2).toInstrSpec (shr_r32_imm8_effect_step 0x109ea7 0xee 0x2 (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x109eaa [0x44, 0x31, 0xD6] (fun s => s.RIP = 0x109eaa) (xorR32R32Effect 0x109eaa 3 6 10)
      [.gpr 6, .gpr 10] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109eaa 3 6 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x109eaa 0x44 0xd6 (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x109ead [0x81, 0xE6, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x109ead) (andR32Imm32Effect 0x109ead 6 6 0x3333)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x109ead 6 6 0x3333).toInstrSpec (and_r32_imm32_effect_step 0x109ead 0xe6 0x3333 (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x109eb3 [0x41, 0x31, 0xF2] (fun s => s.RIP = 0x109eb3) (xorR32R32Effect 0x109eb3 3 10 6)
      [.gpr 10, .gpr 6] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109eb3 3 10 6).toInstrSpec (xor_r32_r32_rex_effect_step 0x109eb3 0x41 0xf2 (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x109eb6 [0xC1, 0xE6, 0x02] (fun s => s.RIP = 0x109eb6) (shlR32Effect 0x109eb6 3 6 2)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR32Effect_footprint 0x109eb6 3 6 2).toInstrSpec (shl_r32_imm8_effect_step 0x109eb6 0xe6 0x2 (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x109eb9 [0x44, 0x31, 0xCE] (fun s => s.RIP = 0x109eb9) (xorR32R32Effect 0x109eb9 3 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109eb9 3 6 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x109eb9 0x44 0xce (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x109ebc [0x88, 0x6F, 0x03] (StorePre 0x109ebc 3 (fun s => AddrMode.addr (.base 7 (.d8 0x3)) s (0x109ebc + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x109ebc 3 5 (.base 7 (.d8 0x3)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x109ebc 3 5 (.base 7 (.d8 0x3))).toInstrSpec (mov_m8_r8_norex_effect_step 0x109ebc 5 (.base 7 (.d8 0x3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f68 : InstrSpec 0x109ebf [0x44, 0x89, 0xC0] (fun s => s.RIP = 0x109ebf) (movR32R32Effect 0x109ebf 3 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x109ebf 3 0 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x109ebf 0x44 0xc0 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x109ec2 [0xC1, 0xE8, 0x02] (fun s => s.RIP = 0x109ec2) (shrR32Effect 0x109ec2 3 0 2)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x109ec2 3 0 2).toInstrSpec (shr_r32_imm8_effect_step 0x109ec2 0xe8 0x2 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x109ec5 [0x31, 0xE8] (fun s => s.RIP = 0x109ec5) (xorR32R32Effect 0x109ec5 2 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109ec5 2 0 5).toInstrSpec (xor_r32_r32_effect_step 0x109ec5 0xe8 (by decide)) pre_rip
  have f71 : InstrSpec 0x109ec7 [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x109ec7) (andEaxImm32Effect 0x109ec7 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x109ec7 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x109ec7 0x3333) pre_rip
  have f72 : InstrSpec 0x109ecc [0x31, 0xC5] (fun s => s.RIP = 0x109ecc) (xorR32R32Effect 0x109ecc 2 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109ecc 2 5 0).toInstrSpec (xor_r32_r32_effect_step 0x109ecc 0xc5 (by decide)) pre_rip
  have f73 : InstrSpec 0x109ece [0xC1, 0xE0, 0x02] (fun s => s.RIP = 0x109ece) (shlR32Effect 0x109ece 3 0 2)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x109ece 3 0 2).toInstrSpec (shl_r32_imm8_effect_step 0x109ece 0xe0 0x2 (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x109ed1 [0x44, 0x31, 0xC0] (fun s => s.RIP = 0x109ed1) (xorR32R32Effect 0x109ed1 3 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109ed1 3 0 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x109ed1 0x44 0xc0 (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x109ed4 [0x89, 0xF1] (fun s => s.RIP = 0x109ed4) (movR32R32Effect 0x109ed4 2 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x109ed4 2 1 6).toInstrSpec (mov_r32_r32_effect_step 0x109ed4 0xf1 (by decide)) pre_rip
  have f76 : InstrSpec 0x109ed6 [0xC1, 0xE9, 0x04] (fun s => s.RIP = 0x109ed6) (shrR32Effect 0x109ed6 3 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x109ed6 3 1 4).toInstrSpec (shr_r32_imm8_effect_step 0x109ed6 0xe9 0x4 (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x109ed9 [0x31, 0xC1] (fun s => s.RIP = 0x109ed9) (xorR32R32Effect 0x109ed9 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109ed9 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x109ed9 0xc1 (by decide)) pre_rip
  have f78 : InstrSpec 0x109edb [0x81, 0xE1, 0x0F, 0x0F, 0x00, 0x00] (fun s => s.RIP = 0x109edb) (andR32Imm32Effect 0x109edb 6 1 0xf0f)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x109edb 6 1 0xf0f).toInstrSpec (and_r32_imm32_effect_step 0x109edb 0xe1 0xf0f (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x109ee1 [0x31, 0xC8] (fun s => s.RIP = 0x109ee1) (xorR32R32Effect 0x109ee1 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109ee1 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x109ee1 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f60 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 165), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 170), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ea7) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f61 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 165), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 172), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eaa) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f62 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 165), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 174), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ead) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.out (n := 176) f63 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 177) (ρ' := [(0, 165), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 176), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eb3) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.out (n := 178) f64 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 179) (ρ' := [(0, 165), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 176), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eb6) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f65 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(0, 165), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 180), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eb9) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f66 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 165), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ebc) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.exec (n := 184) (ρ' := [(0, 165), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ebf) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f68 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 185), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ec2) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f69 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 187), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ec5) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f70 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 189), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ec7) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f71 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 191), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ecc) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f72 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 191), (1, 161), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ece) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f73 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 195), (1, 161), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ed1) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f74 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 197), (1, 161), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ed4) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f75 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 197), (1, 199), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ed6) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f76 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 197), (1, 201), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ed9) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f77 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 204) (ρ' := [(0, 197), (1, 203), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109edb) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 205) (RestInside.out (n := 205) f78 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 206) (ρ' := [(0, 197), (1, 205), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ee1) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 207) (RestInside.out (n := 207) f79 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 208) (ρ' := [(0, 207), (1, 205), (2, 133), (3, 147), (4, 4), (5, 193), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ee3) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109de2_4 code

theorem rest_l109de2_2 [Bindings] (code : CodeMap) :
    Rest (n := 133) code lifted (codeRange 0x109de2 bytes_l109de2) [(0, 65), (1, 81), (2, 95), (3, 123), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 131), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      74 0x109e69 bytes_l109de2_2 b_l109de2_2 := by
  have f40 : InstrSpec 0x109e69 [0x44, 0x31, 0xDA] (fun s => s.RIP = 0x109e69) (xorR32R32Effect 0x109e69 3 2 11)
      [.gpr 2, .gpr 11] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e69 3 2 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x109e69 0x44 0xda (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x109e6c [0x41, 0xC1, 0xE3, 0x02] (fun s => s.RIP = 0x109e6c) (shlR32Effect 0x109e6c 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR32Effect_footprint 0x109e6c 4 11 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x109e6c 0x41 0xe3 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x109e70 [0x41, 0x31, 0xCB] (fun s => s.RIP = 0x109e70) (xorR32R32Effect 0x109e70 3 11 1)
      [.gpr 11, .gpr 1] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e70 3 11 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x109e70 0x41 0xcb (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x109e73 [0x89, 0xF1] (fun s => s.RIP = 0x109e73) (movR32R32Effect 0x109e73 2 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x109e73 2 1 6).toInstrSpec (mov_r32_r32_effect_step 0x109e73 0xf1 (by decide)) pre_rip
  have f44 : InstrSpec 0x109e75 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x109e75) (shrR32Effect 0x109e75 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x109e75 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x109e75 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x109e78 [0x31, 0xD9] (fun s => s.RIP = 0x109e78) (xorR32R32Effect 0x109e78 2 1 3)
      [.gpr 1, .gpr 3] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e78 2 1 3).toInstrSpec (xor_r32_r32_effect_step 0x109e78 0xd9 (by decide)) pre_rip
  have f46 : InstrSpec 0x109e7a [0x81, 0xE1, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x109e7a) (andR32Imm32Effect 0x109e7a 6 1 0x3333)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x109e7a 6 1 0x3333).toInstrSpec (and_r32_imm32_effect_step 0x109e7a 0xe1 0x3333 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x109e80 [0x31, 0xCB] (fun s => s.RIP = 0x109e80) (xorR32R32Effect 0x109e80 2 3 1)
      [.gpr 3, .gpr 1] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e80 2 3 1).toInstrSpec (xor_r32_r32_effect_step 0x109e80 0xcb (by decide)) pre_rip
  have f48 : InstrSpec 0x109e82 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x109e82) (shlR32Effect 0x109e82 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x109e82 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x109e82 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x109e85 [0x31, 0xF1] (fun s => s.RIP = 0x109e85) (xorR32R32Effect 0x109e85 2 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e85 2 1 6).toInstrSpec (xor_r32_r32_effect_step 0x109e85 0xf1 (by decide)) pre_rip
  have f50 : InstrSpec 0x109e87 [0x44, 0x89, 0xD8] (fun s => s.RIP = 0x109e87) (movR32R32Effect 0x109e87 3 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x109e87 3 0 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x109e87 0x44 0xd8 (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x109e8a [0xC1, 0xE8, 0x04] (fun s => s.RIP = 0x109e8a) (shrR32Effect 0x109e8a 3 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x109e8a 3 0 4).toInstrSpec (shr_r32_imm8_effect_step 0x109e8a 0xe8 0x4 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x109e8d [0x31, 0xC8] (fun s => s.RIP = 0x109e8d) (xorR32R32Effect 0x109e8d 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e8d 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x109e8d 0xc8 (by decide)) pre_rip
  have f53 : InstrSpec 0x109e8f [0x25, 0x0F, 0x0F, 0x00, 0x00] (fun s => s.RIP = 0x109e8f) (andEaxImm32Effect 0x109e8f 0xf0f)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x109e8f 0xf0f).toInstrSpec (and_eax_imm32_effect_step 0x109e8f 0xf0f) pre_rip
  have f54 : InstrSpec 0x109e94 [0x31, 0xC1] (fun s => s.RIP = 0x109e94) (xorR32R32Effect 0x109e94 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e94 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x109e94 0xc1 (by decide)) pre_rip
  have f55 : InstrSpec 0x109e96 [0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x109e96) (shlR32Effect 0x109e96 3 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x109e96 3 0 4).toInstrSpec (shl_r32_imm8_effect_step 0x109e96 0xe0 0x4 (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x109e99 [0x44, 0x31, 0xD8] (fun s => s.RIP = 0x109e99) (xorR32R32Effect 0x109e99 3 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e99 3 0 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x109e99 0x44 0xd8 (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x109e9c [0x88, 0x07] (StorePre 0x109e9c 2 (fun s => AddrMode.addr (.base 7 .none) s (0x109e9c + BitVec.ofNat 64 2)) 1) (movM8R8Effect 0x109e9c 2 0 (.base 7 .none))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x109e9c 2 0 (.base 7 .none)).toInstrSpec (mov_m8_r8_effect_step 0x109e9c 0 (by decide) (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f58 : InstrSpec 0x109e9e [0x88, 0x4F, 0x01] (StorePre 0x109e9e 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1)) s (0x109e9e + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109e9e 3 1 (.base 7 (.d8 0x1)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x109e9e 3 1 (.base 7 (.d8 0x1))).toInstrSpec (mov_m8_r8_effect_step 0x109e9e 1 (by decide) (.base 7 (.d8 0x1)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f59 : InstrSpec 0x109ea1 [0x88, 0x67, 0x02] (StorePre 0x109ea1 3 (fun s => AddrMode.addr (.base 7 (.d8 0x2)) s (0x109ea1 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x109ea1 3 4 (.base 7 (.d8 0x2)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x109ea1 3 4 (.base 7 (.d8 0x2))).toInstrSpec (mov_m8_r8_norex_effect_step 0x109ea1 4 (.base 7 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f40 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 65), (1, 81), (2, 133), (3, 123), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 131), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e6c) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f41 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 65), (1, 81), (2, 133), (3, 123), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 135), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e70) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f42 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 65), (1, 81), (2, 133), (3, 123), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e73) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f43 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 65), (1, 139), (2, 133), (3, 123), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e75) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f44 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 65), (1, 141), (2, 133), (3, 123), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e78) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f45 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 65), (1, 143), (2, 133), (3, 123), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e7a) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 65), (1, 145), (2, 133), (3, 123), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e80) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f47 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 65), (1, 145), (2, 133), (3, 147), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e82) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f48 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 65), (1, 149), (2, 133), (3, 147), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e85) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f49 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 65), (1, 151), (2, 133), (3, 147), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e87) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f50 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 153), (1, 151), (2, 133), (3, 147), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e8a) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f51 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 155), (1, 151), (2, 133), (3, 147), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e8d) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f52 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 157), (1, 151), (2, 133), (3, 147), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e8f) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f53 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 159), (1, 151), (2, 133), (3, 147), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e94) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f54 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 159), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e96) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f55 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 163), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e99) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f56 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 165), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e9c) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.exec (n := 167) (ρ' := [(0, 165), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e9e) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 168) (RestInside.exec (n := 168) (ρ' := [(0, 165), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ea1) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 169) (RestInside.exec (n := 169) (ρ' := [(0, 165), (1, 161), (2, 133), (3, 147), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ea4) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l109de2_3 code

theorem rest_l109de2_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x109de2 bytes_l109de2) [(0, 65), (1, 81), (2, 89), (3, 57), (4, 4), (5, 67), (6, 6), (7, 7), (8, 63), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      94 0x109e2b bytes_l109de2_1 b_l109de2_1 := by
  have f20 : InstrSpec 0x109e2b [0x01, 0xD2] (fun s => s.RIP = 0x109e2b) (addR32R32Effect 0x109e2b 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR32R32Effect_footprint 0x109e2b 2 2 2).toInstrSpec (add_r32_r32_effect_step 0x109e2b 0xd2 (by decide)) pre_rip
  have f21 : InstrSpec 0x109e2d [0x31, 0xDA] (fun s => s.RIP = 0x109e2d) (xorR32R32Effect 0x109e2d 2 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e2d 2 2 3).toInstrSpec (xor_r32_r32_effect_step 0x109e2d 0xda (by decide)) pre_rip
  have f22 : InstrSpec 0x109e2f [0x41, 0x0F, 0xB7, 0xF3] (fun s => s.RIP = 0x109e2f) (movzxR32R16Effect 0x109e2f 4 6 11)
      [.gpr 11] [] [.reg 6, .rip] :=
    (movzxR32R16Effect_footprint 0x109e2f 4 6 11).toInstrSpec (movzx_r32_r16_rex_effect_step 0x109e2f 0x41 (by decide) 0xf3 (by decide)) pre_rip
  have f23 : InstrSpec 0x109e33 [0xD1, 0xEE] (fun s => s.RIP = 0x109e33) (shrR32Effect 0x109e33 2 6 1)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x109e33 2 6 1).toInstrSpec (shr_r32_one_effect_step 0x109e33 0xee (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x109e35 [0x44, 0x31, 0xC6] (fun s => s.RIP = 0x109e35) (xorR32R32Effect 0x109e35 3 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e35 3 6 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x109e35 0x44 0xc6 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x109e38 [0x81, 0xE6, 0x55, 0x55, 0x00, 0x00] (fun s => s.RIP = 0x109e38) (andR32Imm32Effect 0x109e38 6 6 0x5555)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x109e38 6 6 0x5555).toInstrSpec (and_r32_imm32_effect_step 0x109e38 0xe6 0x5555 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x109e3e [0x41, 0x31, 0xF0] (fun s => s.RIP = 0x109e3e) (xorR32R32Effect 0x109e3e 3 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e3e 3 8 6).toInstrSpec (xor_r32_r32_rex_effect_step 0x109e3e 0x41 0xf0 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x109e41 [0x01, 0xF6] (fun s => s.RIP = 0x109e41) (addR32R32Effect 0x109e41 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (addR32R32Effect_footprint 0x109e41 2 6 6).toInstrSpec (add_r32_r32_effect_step 0x109e41 0xf6 (by decide)) pre_rip
  have f28 : InstrSpec 0x109e43 [0x44, 0x31, 0xDE] (fun s => s.RIP = 0x109e43) (xorR32R32Effect 0x109e43 3 6 11)
      [.gpr 6, .gpr 11] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e43 3 6 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x109e43 0x44 0xde (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x109e46 [0x89, 0xC3] (fun s => s.RIP = 0x109e46) (movR32R32Effect 0x109e46 2 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x109e46 2 3 0).toInstrSpec (mov_r32_r32_effect_step 0x109e46 0xc3 (by decide)) pre_rip
  have f30 : InstrSpec 0x109e48 [0xD1, 0xEB] (fun s => s.RIP = 0x109e48) (shrR32Effect 0x109e48 2 3 1)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR32Effect_footprint 0x109e48 2 3 1).toInstrSpec (shr_r32_one_effect_step 0x109e48 0xeb (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x109e4a [0x31, 0xEB] (fun s => s.RIP = 0x109e4a) (xorR32R32Effect 0x109e4a 2 3 5)
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e4a 2 3 5).toInstrSpec (xor_r32_r32_effect_step 0x109e4a 0xeb (by decide)) pre_rip
  have f32 : InstrSpec 0x109e4c [0x81, 0xE3, 0x55, 0x55, 0x00, 0x00] (fun s => s.RIP = 0x109e4c) (andR32Imm32Effect 0x109e4c 6 3 0x5555)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x109e4c 6 3 0x5555).toInstrSpec (and_r32_imm32_effect_step 0x109e4c 0xe3 0x5555 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x109e52 [0x31, 0xDD] (fun s => s.RIP = 0x109e52) (xorR32R32Effect 0x109e52 2 5 3)
      [.gpr 5, .gpr 3] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e52 2 5 3).toInstrSpec (xor_r32_r32_effect_step 0x109e52 0xdd (by decide)) pre_rip
  have f34 : InstrSpec 0x109e54 [0x01, 0xDB] (fun s => s.RIP = 0x109e54) (addR32R32Effect 0x109e54 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x109e54 2 3 3).toInstrSpec (add_r32_r32_effect_step 0x109e54 0xdb (by decide)) pre_rip
  have f35 : InstrSpec 0x109e56 [0x31, 0xC3] (fun s => s.RIP = 0x109e56) (xorR32R32Effect 0x109e56 2 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e56 2 3 0).toInstrSpec (xor_r32_r32_effect_step 0x109e56 0xc3 (by decide)) pre_rip
  have f36 : InstrSpec 0x109e58 [0x41, 0x89, 0xCB] (fun s => s.RIP = 0x109e58) (movR32R32Effect 0x109e58 3 11 1)
      [.gpr 1] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x109e58 3 11 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x109e58 0x41 0xcb (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x109e5b [0x41, 0xC1, 0xEB, 0x02] (fun s => s.RIP = 0x109e5b) (shrR32Effect 0x109e5b 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x109e5b 4 11 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x109e5b 0x41 0xeb 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x109e5f [0x41, 0x31, 0xD3] (fun s => s.RIP = 0x109e5f) (xorR32R32Effect 0x109e5f 3 11 2)
      [.gpr 11, .gpr 2] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e5f 3 11 2).toInstrSpec (xor_r32_r32_rex_effect_step 0x109e5f 0x41 0xd3 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x109e62 [0x41, 0x81, 0xE3, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x109e62) (andR32Imm32Effect 0x109e62 7 11 0x3333)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x109e62 7 11 0x3333).toInstrSpec (and_r32_imm32_rex_effect_step 0x109e62 0x41 0xe3 0x3333 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 65), (1, 81), (2, 93), (3, 57), (4, 4), (5, 67), (6, 6), (7, 7), (8, 63), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e2d) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 57), (4, 4), (5, 67), (6, 6), (7, 7), (8, 63), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e2f) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 57), (4, 4), (5, 67), (6, 97), (7, 7), (8, 63), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e33) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 57), (4, 4), (5, 67), (6, 99), (7, 7), (8, 63), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e35) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 57), (4, 4), (5, 67), (6, 101), (7, 7), (8, 63), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e38) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 57), (4, 4), (5, 67), (6, 103), (7, 7), (8, 63), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e3e) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 57), (4, 4), (5, 67), (6, 103), (7, 7), (8, 105), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e41) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 57), (4, 4), (5, 67), (6, 107), (7, 7), (8, 105), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e43) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 57), (4, 4), (5, 67), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e46) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 111), (4, 4), (5, 67), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e48) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 113), (4, 4), (5, 67), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e4a) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 115), (4, 4), (5, 67), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e4c) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f32 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 117), (4, 4), (5, 67), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e52) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f33 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 117), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e54) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f34 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 121), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e56) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f35 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 123), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e58) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f36 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 123), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 125), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e5b) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f37 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 123), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 127), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e5f) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f38 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 123), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 129), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e62) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f39 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 65), (1, 81), (2, 95), (3, 123), (4, 4), (5, 119), (6, 109), (7, 7), (8, 105), (9, 77), (10, 91), (11, 131), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e69) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109de2_2 code

theorem rest_l109de2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109de2 bytes_l109de2) (entryMap (live .l109de2))
      114 0x109de2 bytes_l109de2 b_l109de2 := by
  have f0 : InstrSpec 0x109de2 [0x0F, 0xB7, 0x16] (LoadPre 0x109de2 (fun s => AddrMode.addr (.base 6 .none) s (0x109de2 + BitVec.ofNat 64 3)) 2) (movzxR32M16Effect 0x109de2 3 2 (.base 6 .none))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x109de2 3 2 (.base 6 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x109de2 2 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x109de5 [0x44, 0x0F, 0xB7, 0x4E, 0x02] (LoadPre 0x109de5 (fun s => AddrMode.addr (.base 6 (.d8 0x2)) s (0x109de5 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x109de5 5 9 (.base 6 (.d8 0x2)))
      [.gpr 6] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x109de5 5 9 (.base 6 (.d8 0x2))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x109de5 0x44 (by decide) 1 (.base 6 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x109dea [0x0F, 0xB7, 0x5E, 0x04] (LoadPre 0x109dea (fun s => AddrMode.addr (.base 6 (.d8 0x4)) s (0x109dea + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x109dea 4 3 (.base 6 (.d8 0x4)))
      [.gpr 6] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x109dea 4 3 (.base 6 (.d8 0x4))).toInstrSpec (movzx_r32_m16_effect_step 0x109dea 3 (.base 6 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x109dee [0x44, 0x0F, 0xB7, 0x56, 0x06] (LoadPre 0x109dee (fun s => AddrMode.addr (.base 6 (.d8 0x6)) s (0x109dee + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x109dee 5 10 (.base 6 (.d8 0x6)))
      [.gpr 6] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x109dee 5 10 (.base 6 (.d8 0x6))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x109dee 0x44 (by decide) 2 (.base 6 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x109df3 [0x44, 0x0F, 0xB7, 0x5E, 0x08] (LoadPre 0x109df3 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109df3 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x109df3 5 11 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 11, .rip] :=
    (movzxR32M16Effect_footprint 0x109df3 5 11 (.base 6 (.d8 0x8))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x109df3 0x44 (by decide) 3 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x109df8 [0x44, 0x0F, 0xB7, 0x46, 0x0A] (LoadPre 0x109df8 (fun s => AddrMode.addr (.base 6 (.d8 0xa)) s (0x109df8 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x109df8 5 8 (.base 6 (.d8 0xa)))
      [.gpr 6] [] [.reg 8, .rip] :=
    (movzxR32M16Effect_footprint 0x109df8 5 8 (.base 6 (.d8 0xa))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x109df8 0x44 (by decide) 0 (.base 6 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x109dfd [0x0F, 0xB7, 0x46, 0x0C] (LoadPre 0x109dfd (fun s => AddrMode.addr (.base 6 (.d8 0xc)) s (0x109dfd + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x109dfd 4 0 (.base 6 (.d8 0xc)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x109dfd 4 0 (.base 6 (.d8 0xc))).toInstrSpec (movzx_r32_m16_effect_step 0x109dfd 0 (.base 6 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x109e01 [0x0F, 0xB7, 0x6E, 0x0E] (LoadPre 0x109e01 (fun s => AddrMode.addr (.base 6 (.d8 0xe)) s (0x109e01 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x109e01 4 5 (.base 6 (.d8 0xe)))
      [.gpr 6] [] [.reg 5, .rip] :=
    (movzxR32M16Effect_footprint 0x109e01 4 5 (.base 6 (.d8 0xe))).toInstrSpec (movzx_r32_m16_effect_step 0x109e01 5 (.base 6 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x109e05 [0x0F, 0xB7, 0xCA] (fun s => s.RIP = 0x109e05) (movzxR32R16Effect 0x109e05 3 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32R16Effect_footprint 0x109e05 3 1 2).toInstrSpec (movzx_r32_r16_effect_step 0x109e05 0xca (by decide)) pre_rip
  have f9 : InstrSpec 0x109e08 [0xD1, 0xE9] (fun s => s.RIP = 0x109e08) (shrR32Effect 0x109e08 2 1 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x109e08 2 1 1).toInstrSpec (shr_r32_one_effect_step 0x109e08 0xe9 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x109e0a [0x44, 0x31, 0xC9] (fun s => s.RIP = 0x109e0a) (xorR32R32Effect 0x109e0a 3 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e0a 3 1 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x109e0a 0x44 0xc9 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x109e0d [0x81, 0xE1, 0x55, 0x55, 0x00, 0x00] (fun s => s.RIP = 0x109e0d) (andR32Imm32Effect 0x109e0d 6 1 0x5555)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x109e0d 6 1 0x5555).toInstrSpec (and_r32_imm32_effect_step 0x109e0d 0xe1 0x5555 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x109e13 [0x41, 0x31, 0xC9] (fun s => s.RIP = 0x109e13) (xorR32R32Effect 0x109e13 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e13 3 9 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x109e13 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x109e16 [0x01, 0xC9] (fun s => s.RIP = 0x109e16) (addR32R32Effect 0x109e16 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR32R32Effect_footprint 0x109e16 2 1 1).toInstrSpec (add_r32_r32_effect_step 0x109e16 0xc9 (by decide)) pre_rip
  have f14 : InstrSpec 0x109e18 [0x31, 0xD1] (fun s => s.RIP = 0x109e18) (xorR32R32Effect 0x109e18 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e18 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x109e18 0xd1 (by decide)) pre_rip
  have f15 : InstrSpec 0x109e1a [0x0F, 0xB7, 0xD3] (fun s => s.RIP = 0x109e1a) (movzxR32R16Effect 0x109e1a 3 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movzxR32R16Effect_footprint 0x109e1a 3 2 3).toInstrSpec (movzx_r32_r16_effect_step 0x109e1a 0xd3 (by decide)) pre_rip
  have f16 : InstrSpec 0x109e1d [0xD1, 0xEA] (fun s => s.RIP = 0x109e1d) (shrR32Effect 0x109e1d 2 2 1)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x109e1d 2 2 1).toInstrSpec (shr_r32_one_effect_step 0x109e1d 0xea (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x109e1f [0x44, 0x31, 0xD2] (fun s => s.RIP = 0x109e1f) (xorR32R32Effect 0x109e1f 3 2 10)
      [.gpr 2, .gpr 10] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e1f 3 2 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x109e1f 0x44 0xd2 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x109e22 [0x81, 0xE2, 0x55, 0x55, 0x00, 0x00] (fun s => s.RIP = 0x109e22) (andR32Imm32Effect 0x109e22 6 2 0x5555)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x109e22 6 2 0x5555).toInstrSpec (and_r32_imm32_effect_step 0x109e22 0xe2 0x5555 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x109e28 [0x41, 0x31, 0xD2] (fun s => s.RIP = 0x109e28) (xorR32R32Effect 0x109e28 3 10 2)
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109e28 3 10 2).toInstrSpec (xor_r32_r32_rex_effect_step 0x109e28 0x41 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (4, 4), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109de5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (4, 4), (6, 6), (7, 7), (9, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109dea) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 53), (3, 57), (4, 4), (6, 6), (7, 7), (9, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109dee) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 53), (3, 57), (4, 4), (6, 6), (7, 7), (9, 55), (10, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109df3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 53), (3, 57), (4, 4), (6, 6), (7, 7), (9, 55), (10, 59), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109df8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 53), (3, 57), (4, 4), (6, 6), (7, 7), (8, 63), (9, 55), (10, 59), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109dfd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (2, 53), (3, 57), (4, 4), (6, 6), (7, 7), (8, 63), (9, 55), (10, 59), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e01) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (2, 53), (3, 57), (4, 4), (5, 67), (6, 6), (7, 7), (8, 63), (9, 55), (10, 59), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e05) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 69), (2, 53), (3, 57), (4, 4), (5, 67), (6, 6), (7, 7), (8, 63), (9, 55), (10, 59), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e08) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 65), (1, 71), (2, 53), (3, 57), (4, 4), (5, 67), (6, 6), (7, 7), (8, 63), (9, 55), (10, 59), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e0a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 65), (1, 73), (2, 53), (3, 57), (4, 4), (5, 67), (6, 6), (7, 7), (8, 63), (9, 55), (10, 59), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e0d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 65), (1, 75), (2, 53), (3, 57), (4, 4), (5, 67), (6, 6), (7, 7), (8, 63), (9, 55), (10, 59), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e13) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 65), (1, 75), (2, 53), (3, 57), (4, 4), (5, 67), (6, 6), (7, 7), (8, 63), (9, 77), (10, 59), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e16) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 65), (1, 79), (2, 53), (3, 57), (4, 4), (5, 67), (6, 6), (7, 7), (8, 63), (9, 77), (10, 59), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e18) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 65), (1, 81), (2, 53), (3, 57), (4, 4), (5, 67), (6, 6), (7, 7), (8, 63), (9, 77), (10, 59), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e1a) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 65), (1, 81), (2, 83), (3, 57), (4, 4), (5, 67), (6, 6), (7, 7), (8, 63), (9, 77), (10, 59), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e1d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 65), (1, 81), (2, 85), (3, 57), (4, 4), (5, 67), (6, 6), (7, 7), (8, 63), (9, 77), (10, 59), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e1f) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 65), (1, 81), (2, 87), (3, 57), (4, 4), (5, 67), (6, 6), (7, 7), (8, 63), (9, 77), (10, 59), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e22) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 65), (1, 81), (2, 89), (3, 57), (4, 4), (5, 67), (6, 6), (7, 7), (8, 63), (9, 77), (10, 59), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e28) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 65), (1, 81), (2, 89), (3, 57), (4, 4), (5, 67), (6, 6), (7, 7), (8, 63), (9, 77), (10, 91), (11, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e2b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109de2_1 code

theorem block_l109de2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109de2 :=
  Rest.liftedBlock (rest_l109de2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109de2 x hx)

theorem rest_l109f41 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109f41 bytes_l109f41) (entryMap (live .l109f41))
      4 0x109f41 bytes_l109f41 b_l109f41 := by
  have f0 : InstrSpec 0x109f41 [0x31, 0xFF] (fun s => s.RIP = 0x109f41) (xorR32R32Effect 0x109f41 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109f41 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x109f41 0xff (by decide)) pre_rip
  have f1 : InstrSpec 0x109f43 [0x31, 0xF6] (fun s => s.RIP = 0x109f43) (xorR32R32Effect 0x109f43 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109f43 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x109f43 0xf6 (by decide)) pre_rip
  have f2 : InstrSpec 0x109f45 [0x48, 0xC7, 0xC2, 0x58, 0x10, 0x20, 0x00] (fun s => s.RIP = 0x109f45) (movR64Imm32Effect 0x109f45 2 0x201058)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x109f45 2 0x201058).toInstrSpec (mov_r64_imm32_effect_step 0x109f45 0x48 0xc2 (by decide) (by decide) (by decide) 0x201058) pre_rip
  have f3 : InstrSpec 0x109f4c [0xE8, 0xE6, 0x98, 0xFF, 0xFF] (PushPre 0x109f4c 5) (callEffect (fun _ => 0x103837) 0x109f51)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109f4c 0x103837 0x109f51).toInstrSpec (call_rel32_effect_step 0x109f4c 0xffff98e6 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x109f43) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x109f45) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x109f4c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l109f41 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109f41 :=
  Rest.liftedBlock (rest_l109f41 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109f41 x hx)

theorem rest_l109f51 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109f51 bytes_l109f51) (entryMap (live .l109f51))
      4 0x109f51 bytes_l109f51 b_l109f51 := by
  have f0 : InstrSpec 0x109f51 [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109f51) (movR32Imm32Effect 0x109f51 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x109f51 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x109f51 0xbf (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x109f56 [0xBE, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109f56) (movR32Imm32Effect 0x109f56 5 6 0x1)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x109f56 5 6 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x109f56 0xbe (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x109f5b [0x48, 0xC7, 0xC2, 0x70, 0x10, 0x20, 0x00] (fun s => s.RIP = 0x109f5b) (movR64Imm32Effect 0x109f5b 2 0x201070)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x109f5b 2 0x201070).toInstrSpec (mov_r64_imm32_effect_step 0x109f5b 0x48 0xc2 (by decide) (by decide) (by decide) 0x201070) pre_rip
  have f3 : InstrSpec 0x109f62 [0xE8, 0xD0, 0x98, 0xFF, 0xFF] (PushPre 0x109f62 5) (callEffect (fun _ => 0x103837) 0x109f67)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109f62 0x103837 0x109f67).toInstrSpec (call_rel32_effect_step 0x109f62 0xffff98d0 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x109f56) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x109f5b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x109f62) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l109f51 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109f51 :=
  Rest.liftedBlock (rest_l109f51 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109f51 x hx)

theorem rest_l109f67 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109f67 bytes_l109f67) (entryMap (live .l109f67))
      4 0x109f67 bytes_l109f67 b_l109f67 := by
  have f0 : InstrSpec 0x109f67 [0xBF, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109f67) (movR32Imm32Effect 0x109f67 5 7 0x2)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x109f67 5 7 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x109f67 0xbf (by decide) 0x2) pre_rip
  have f1 : InstrSpec 0x109f6c [0xBE, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109f6c) (movR32Imm32Effect 0x109f6c 5 6 0x2)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x109f6c 5 6 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x109f6c 0xbe (by decide) 0x2) pre_rip
  have f2 : InstrSpec 0x109f71 [0x48, 0xC7, 0xC2, 0x88, 0x10, 0x20, 0x00] (fun s => s.RIP = 0x109f71) (movR64Imm32Effect 0x109f71 2 0x201088)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x109f71 2 0x201088).toInstrSpec (mov_r64_imm32_effect_step 0x109f71 0x48 0xc2 (by decide) (by decide) (by decide) 0x201088) pre_rip
  have f3 : InstrSpec 0x109f78 [0xE8, 0xBA, 0x98, 0xFF, 0xFF] (PushPre 0x109f78 5) (callEffect (fun _ => 0x103837) 0x109f7d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109f78 0x103837 0x109f7d).toInstrSpec (call_rel32_effect_step 0x109f78 0xffff98ba (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x109f6c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x109f71) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x109f78) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l109f67 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109f67 :=
  Rest.liftedBlock (rest_l109f67 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109f67 x hx)

theorem rest_l109f7d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109f7d bytes_l109f7d) (entryMap (live .l109f7d))
      4 0x109f7d bytes_l109f7d b_l109f7d := by
  have f0 : InstrSpec 0x109f7d [0xBF, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109f7d) (movR32Imm32Effect 0x109f7d 5 7 0x3)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x109f7d 5 7 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x109f7d 0xbf (by decide) 0x3) pre_rip
  have f1 : InstrSpec 0x109f82 [0xBE, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109f82) (movR32Imm32Effect 0x109f82 5 6 0x3)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x109f82 5 6 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x109f82 0xbe (by decide) 0x3) pre_rip
  have f2 : InstrSpec 0x109f87 [0x48, 0xC7, 0xC2, 0xA0, 0x10, 0x20, 0x00] (fun s => s.RIP = 0x109f87) (movR64Imm32Effect 0x109f87 2 0x2010a0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x109f87 2 0x2010a0).toInstrSpec (mov_r64_imm32_effect_step 0x109f87 0x48 0xc2 (by decide) (by decide) (by decide) 0x2010a0) pre_rip
  have f3 : InstrSpec 0x109f8e [0xE8, 0xA4, 0x98, 0xFF, 0xFF] (PushPre 0x109f8e 5) (callEffect (fun _ => 0x103837) 0x109f93)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109f8e 0x103837 0x109f93).toInstrSpec (call_rel32_effect_step 0x109f8e 0xffff98a4 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x109f82) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x109f87) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x109f8e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l109f7d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109f7d :=
  Rest.liftedBlock (rest_l109f7d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109f7d x hx)

theorem rest_l109f93 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109f93 bytes_l109f93) (entryMap (live .l109f93))
      4 0x109f93 bytes_l109f93 b_l109f93 := by
  have f0 : InstrSpec 0x109f93 [0xBF, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109f93) (movR32Imm32Effect 0x109f93 5 7 0x4)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x109f93 5 7 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x109f93 0xbf (by decide) 0x4) pre_rip
  have f1 : InstrSpec 0x109f98 [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109f98) (movR32Imm32Effect 0x109f98 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x109f98 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x109f98 0xbe (by decide) 0x4) pre_rip
  have f2 : InstrSpec 0x109f9d [0x48, 0xC7, 0xC2, 0xB8, 0x10, 0x20, 0x00] (fun s => s.RIP = 0x109f9d) (movR64Imm32Effect 0x109f9d 2 0x2010b8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x109f9d 2 0x2010b8).toInstrSpec (mov_r64_imm32_effect_step 0x109f9d 0x48 0xc2 (by decide) (by decide) (by decide) 0x2010b8) pre_rip
  have f3 : InstrSpec 0x109fa4 [0xE8, 0x8E, 0x98, 0xFF, 0xFF] (PushPre 0x109fa4 5) (callEffect (fun _ => 0x103837) 0x109fa9)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109fa4 0x103837 0x109fa9).toInstrSpec (call_rel32_effect_step 0x109fa4 0xffff988e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x109f98) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x109f9d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x109fa4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l109f93 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109f93 :=
  Rest.liftedBlock (rest_l109f93 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109f93 x hx)

theorem rest_l109fa9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109fa9 bytes_l109fa9) (entryMap (live .l109fa9))
      4 0x109fa9 bytes_l109fa9 b_l109fa9 := by
  have f0 : InstrSpec 0x109fa9 [0xBF, 0x05, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109fa9) (movR32Imm32Effect 0x109fa9 5 7 0x5)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x109fa9 5 7 0x5).toInstrSpec (mov_r32_imm32_effect_step 0x109fa9 0xbf (by decide) 0x5) pre_rip
  have f1 : InstrSpec 0x109fae [0xBE, 0x05, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109fae) (movR32Imm32Effect 0x109fae 5 6 0x5)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x109fae 5 6 0x5).toInstrSpec (mov_r32_imm32_effect_step 0x109fae 0xbe (by decide) 0x5) pre_rip
  have f2 : InstrSpec 0x109fb3 [0x48, 0xC7, 0xC2, 0xD0, 0x10, 0x20, 0x00] (fun s => s.RIP = 0x109fb3) (movR64Imm32Effect 0x109fb3 2 0x2010d0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x109fb3 2 0x2010d0).toInstrSpec (mov_r64_imm32_effect_step 0x109fb3 0x48 0xc2 (by decide) (by decide) (by decide) 0x2010d0) pre_rip
  have f3 : InstrSpec 0x109fba [0xE8, 0x78, 0x98, 0xFF, 0xFF] (PushPre 0x109fba 5) (callEffect (fun _ => 0x103837) 0x109fbf)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109fba 0x103837 0x109fbf).toInstrSpec (call_rel32_effect_step 0x109fba 0xffff9878 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x109fae) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x109fb3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x109fba) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l109fa9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109fa9 :=
  Rest.liftedBlock (rest_l109fa9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109fa9 x hx)

theorem rest_l109fbf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109fbf bytes_l109fbf) (entryMap (live .l109fbf))
      4 0x109fbf bytes_l109fbf b_l109fbf := by
  have f0 : InstrSpec 0x109fbf [0xBF, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109fbf) (movR32Imm32Effect 0x109fbf 5 7 0x6)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x109fbf 5 7 0x6).toInstrSpec (mov_r32_imm32_effect_step 0x109fbf 0xbf (by decide) 0x6) pre_rip
  have f1 : InstrSpec 0x109fc4 [0xBE, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109fc4) (movR32Imm32Effect 0x109fc4 5 6 0x6)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x109fc4 5 6 0x6).toInstrSpec (mov_r32_imm32_effect_step 0x109fc4 0xbe (by decide) 0x6) pre_rip
  have f2 : InstrSpec 0x109fc9 [0x48, 0xC7, 0xC2, 0xE8, 0x10, 0x20, 0x00] (fun s => s.RIP = 0x109fc9) (movR64Imm32Effect 0x109fc9 2 0x2010e8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x109fc9 2 0x2010e8).toInstrSpec (mov_r64_imm32_effect_step 0x109fc9 0x48 0xc2 (by decide) (by decide) (by decide) 0x2010e8) pre_rip
  have f3 : InstrSpec 0x109fd0 [0xE8, 0x62, 0x98, 0xFF, 0xFF] (PushPre 0x109fd0 5) (callEffect (fun _ => 0x103837) 0x109fd5)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109fd0 0x103837 0x109fd5).toInstrSpec (call_rel32_effect_step 0x109fd0 0xffff9862 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x109fc4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x109fc9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x109fd0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l109fbf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109fbf :=
  Rest.liftedBlock (rest_l109fbf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109fbf x hx)

theorem rest_l109fd5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109fd5 bytes_l109fd5) (entryMap (live .l109fd5))
      4 0x109fd5 bytes_l109fd5 b_l109fd5 := by
  have f0 : InstrSpec 0x109fd5 [0xBF, 0x07, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109fd5) (movR32Imm32Effect 0x109fd5 5 7 0x7)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x109fd5 5 7 0x7).toInstrSpec (mov_r32_imm32_effect_step 0x109fd5 0xbf (by decide) 0x7) pre_rip
  have f1 : InstrSpec 0x109fda [0xBE, 0x07, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109fda) (movR32Imm32Effect 0x109fda 5 6 0x7)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x109fda 5 6 0x7).toInstrSpec (mov_r32_imm32_effect_step 0x109fda 0xbe (by decide) 0x7) pre_rip
  have f2 : InstrSpec 0x109fdf [0x48, 0xC7, 0xC2, 0x00, 0x11, 0x20, 0x00] (fun s => s.RIP = 0x109fdf) (movR64Imm32Effect 0x109fdf 2 0x201100)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x109fdf 2 0x201100).toInstrSpec (mov_r64_imm32_effect_step 0x109fdf 0x48 0xc2 (by decide) (by decide) (by decide) 0x201100) pre_rip
  have f3 : InstrSpec 0x109fe6 [0xE8, 0x4C, 0x98, 0xFF, 0xFF] (PushPre 0x109fe6 5) (callEffect (fun _ => 0x103837) 0x109feb)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109fe6 0x103837 0x109feb).toInstrSpec (call_rel32_effect_step 0x109fe6 0xffff984c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x109fda) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x109fdf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x109fe6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l109fd5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109fd5 :=
  Rest.liftedBlock (rest_l109fd5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109fd5 x hx)

theorem rest_l109feb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109feb bytes_l109feb) (entryMap (live .l109feb))
      1 0x109feb bytes_l109feb b_l109feb := by
  have f0 : InstrSpec 0x109feb [0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x109feb) (fun _ => nopEffect 0x109feb 5)
      [] [] [.rip] :=
    (nopEffect_footprint 0x109feb 5).toInstrSpec (nop_m_effect_step 0x109feb [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ff0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l109feb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109feb :=
  Rest.liftedBlock (rest_l109feb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109feb x hx)

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

theorem_by block_l109d90_eval :
    program.runBlock (dialect code) ⟨.l109d90, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109d9c_eval :
    program.runBlock (dialect code) ⟨.l109d9c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109da6_eval :
    program.runBlock (dialect code) ⟨.l109da6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109db0_eval :
    program.runBlock (dialect code) ⟨.l109db0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109dba_eval :
    program.runBlock (dialect code) ⟨.l109dba, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109dc4_eval :
    program.runBlock (dialect code) ⟨.l109dc4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109dce_eval :
    program.runBlock (dialect code) ⟨.l109dce, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109dd8_eval :
    program.runBlock (dialect code) ⟨.l109dd8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109de2_eval :
    program.runBlock (dialect code) ⟨.l109de2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109f41_eval :
    program.runBlock (dialect code) ⟨.l109f41, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109f51_eval :
    program.runBlock (dialect code) ⟨.l109f51, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109f67_eval :
    program.runBlock (dialect code) ⟨.l109f67, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109f7d_eval :
    program.runBlock (dialect code) ⟨.l109f7d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109f93_eval :
    program.runBlock (dialect code) ⟨.l109f93, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109fa9_eval :
    program.runBlock (dialect code) ⟨.l109fa9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109fbf_eval :
    program.runBlock (dialect code) ⟨.l109fbf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109fd5_eval :
    program.runBlock (dialect code) ⟨.l109fd5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109feb_eval :
    program.runBlock (dialect code) ⟨.l109feb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
