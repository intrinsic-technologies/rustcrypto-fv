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

theorem rest_l1065b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1065b0 bytes_l1065b0) (entryMap (live .l1065b0))
      9 0x1065b0 bytes_l1065b0 b_l1065b0 := by
  have f0 : InstrSpec 0x1065b0 [0x55] (PushPre 0x1065b0 1) (pushR64Effect 0x1065b0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1065b0 1 5).toInstrSpec (push_r64_effect_step 0x1065b0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1065b1 [0x41, 0x57] (PushPre 0x1065b1 2) (pushR64Effect 0x1065b1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1065b1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1065b1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1065b3 [0x41, 0x56] (PushPre 0x1065b3 2) (pushR64Effect 0x1065b3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1065b3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1065b3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1065b5 [0x41, 0x55] (PushPre 0x1065b5 2) (pushR64Effect 0x1065b5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1065b5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1065b5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1065b7 [0x41, 0x54] (PushPre 0x1065b7 2) (pushR64Effect 0x1065b7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1065b7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1065b7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1065b9 [0x53] (PushPre 0x1065b9 1) (pushR64Effect 0x1065b9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1065b9 1 3).toInstrSpec (push_r64_effect_step 0x1065b9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1065ba [0x48, 0x83, 0xEC, 0x18] (fun s => s.RIP = 0x1065ba) (subR64Imm8Effect 0x1065ba 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1065ba 4 0x18).toInstrSpec (sub_r64_imm8_effect_step 0x1065ba 0x48 0xec 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1065be [0x81, 0xFA, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1065be) (cmpR32Imm32Effect 0x1065be 6 2 0x100)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm32Effect_footprint 0x1065be 6 2 0x100).toInstrSpec (cmp_r32_imm32_effect_step 0x1065be 0xfa 0x100 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065b1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065b3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065b5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065b7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065b9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065ba) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065be) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065c4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 69) (jcc_rel32_effect_step 0x1065c4 3 0x19a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1065b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1065b0 :=
  Rest.liftedBlock (rest_l1065b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1065b0 x hx)

theorem rest_l1065ca_1 [Bindings] (code : CodeMap) :
    Rest (n := 86) code lifted (codeRange 0x1065ca bytes_l1065ca) [(0, 66), (1, 84), (2, 2), (3, 60), (4, 4), (5, 80), (7, 7), (9, 70), (10, 58), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]
      18 0x10661b bytes_l1065ca_1 b_l1065ca_1 := by
  have f20 : InstrSpec 0x10661b [0x88, 0x4C, 0x24, 0x0B] (StorePre 0x10661b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x10661b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10661b 4 1 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10661b 4 1 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (mov_m8_r8_effect_step 0x10661b 1 (by decide) (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x10661f [0x0F, 0xB6, 0x44, 0x24, 0x0B] (LoadPre 0x10661f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x10661f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10661f 5 0 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10661f 5 0 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (movzx_r32_m8_effect_step 0x10661f 0 (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x106624 [0x88, 0x4C, 0x24, 0x0B] (StorePre 0x106624 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x106624 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106624 4 1 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x106624 4 1 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (mov_m8_r8_effect_step 0x106624 1 (by decide) (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x106628 [0x0F, 0xB6, 0x74, 0x24, 0x0B] (LoadPre 0x106628 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x106628 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106628 5 6 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x106628 5 6 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (movzx_r32_m8_effect_step 0x106628 6 (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x10662d [0x88, 0x4C, 0x24, 0x0D] (StorePre 0x10662d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x10662d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10662d 4 1 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10662d 4 1 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (mov_m8_r8_effect_step 0x10662d 1 (by decide) (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x106631 [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x0D] (LoadPre 0x106631 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x106631 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x106631 6 8 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x106631 6 8 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x106631 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x106637 [0x88, 0x4C, 0x24, 0x0D] (StorePre 0x106637 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x106637 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106637 4 1 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x106637 4 1 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (mov_m8_r8_effect_step 0x106637 1 (by decide) (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x10663b [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x0D] (LoadPre 0x10663b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x10663b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10663b 6 11 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x10663b 6 11 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10663b 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x106641 [0x83, 0xE2, 0x3F] (fun s => s.RIP = 0x106641) (andR32Imm8Effect 0x106641 3 2 0x3f)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x106641 3 2 0x3f).toInstrSpec (and_r32_imm8_effect_step 0x106641 0xe2 0x3f (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x106644 [0x0F, 0x95, 0x44, 0x24, 0x0E] (StorePre 0x106644 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106644 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x106644 5 (.sib 4 none 0 (.d8 0xe))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x106644 5 (.sib 4 none 0 (.d8 0xe)) 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x106644 5 0 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x106649 [0x40, 0x0F, 0x95, 0xC7] (fun s => s.RIP = 0x106649) (atFlags (condHolds 5) (setccR8Effect 0x106649 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x106649 4 7 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x106649 5 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f31 : InstrSpec 0x10664d [0x48, 0x8D, 0x4C, 0x24, 0x0E] (fun s => s.RIP = 0x10664d) (leaR64Effect 0x10664d 1 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x10664d 1 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (lea_r64_effect_step 0x10664d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x106652 [0x0F, 0xB6, 0x4C, 0x24, 0x0E] (LoadPre 0x106652 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106652 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106652 5 1 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x106652 5 1 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m8_effect_step 0x106652 1 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x106657 [0xF7, 0xD9] (fun s => s.RIP = 0x106657) (negR32Effect 0x106657 2 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR32Effect_footprint 0x106657 2 1).toInstrSpec (neg_r32_effect_step 0x106657 0xd9 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x106659 [0x83, 0xF2, 0x01] (fun s => s.RIP = 0x106659) (xorR32Imm8Effect 0x106659 3 2 0x1)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x106659 3 2 0x1).toInstrSpec (xor_r32_imm8_effect_step 0x106659 0xf2 0x1 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x10665c [0x21, 0xCA] (fun s => s.RIP = 0x10665c) (andR32R32Effect 0x10665c 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (andR32R32Effect_footprint 0x10665c 2 2 1).toInstrSpec (and_r32_r32_effect_step 0x10665c 0xca (by decide)) pre_rip
  have f36 : InstrSpec 0x10665e [0x83, 0xFA, 0x01] (fun s => s.RIP = 0x10665e) (cmpR32Imm8Effect 0x10665e 3 2 0x1)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x10665e 3 2 0x1).toInstrSpec (cmp_r32_imm8_effect_step 0x10665e 0xfa 0x1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 66), (1, 84), (2, 2), (3, 60), (4, 4), (5, 80), (7, 7), (9, 70), (10, 58), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10661f) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 84), (2, 2), (3, 60), (4, 4), (5, 80), (7, 7), (9, 70), (10, 58), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106624) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 87), (1, 84), (2, 2), (3, 60), (4, 4), (5, 80), (7, 7), (9, 70), (10, 58), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106628) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f23 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 87), (1, 84), (2, 2), (3, 60), (4, 4), (5, 80), (6, 90), (7, 7), (9, 70), (10, 58), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10662d) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 87), (1, 84), (2, 2), (3, 60), (4, 4), (5, 80), (6, 90), (7, 7), (9, 70), (10, 58), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106631) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f25 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 87), (1, 84), (2, 2), (3, 60), (4, 4), (5, 80), (6, 90), (7, 7), (8, 93), (9, 70), (10, 58), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106637) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 87), (1, 84), (2, 2), (3, 60), (4, 4), (5, 80), (6, 90), (7, 7), (8, 93), (9, 70), (10, 58), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10663b) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f27 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 87), (1, 84), (2, 2), (3, 60), (4, 4), (5, 80), (6, 90), (7, 7), (8, 93), (9, 70), (10, 58), (11, 96), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106641) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f28 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 99) f28 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 100) (ρ' := [(0, 87), (1, 84), (2, 98), (3, 60), (4, 4), (5, 80), (6, 90), (7, 7), (8, 93), (9, 70), (10, 58), (11, 96), (12, 73), (13, 54), (14, 76), (15, 56), (19, 99), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106644) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 87), (1, 84), (2, 98), (3, 60), (4, 4), (5, 80), (6, 90), (7, 7), (8, 93), (9, 70), (10, 58), (11, 96), (12, 73), (13, 54), (14, 76), (15, 56), (19, 99), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106649) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f30 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 87), (1, 84), (2, 98), (3, 60), (4, 4), (5, 80), (6, 90), (7, 102), (8, 93), (9, 70), (10, 58), (11, 96), (12, 73), (13, 54), (14, 76), (15, 56), (19, 99), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10664d) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 87), (2, 98), (3, 60), (4, 4), (5, 80), (6, 90), (7, 102), (8, 93), (9, 70), (10, 58), (11, 96), (12, 73), (13, 54), (14, 76), (15, 56), (19, 99), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106652) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f32 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 87), (1, 105), (2, 98), (3, 60), (4, 4), (5, 80), (6, 90), (7, 102), (8, 93), (9, 70), (10, 58), (11, 96), (12, 73), (13, 54), (14, 76), (15, 56), (19, 99), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106657) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f33 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 87), (1, 107), (2, 98), (3, 60), (4, 4), (5, 80), (6, 90), (7, 102), (8, 93), (9, 70), (10, 58), (11, 96), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106659) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f34 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 87), (1, 107), (2, 109), (3, 60), (4, 4), (5, 80), (6, 90), (7, 102), (8, 93), (9, 70), (10, 58), (11, 96), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10665c) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f35 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 87), (1, 107), (2, 111), (3, 60), (4, 4), (5, 80), (6, 90), (7, 102), (8, 93), (9, 70), (10, 58), (11, 96), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10665e) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f36 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 87), (1, 107), (2, 111), (3, 60), (4, 4), (5, 80), (6, 90), (7, 102), (8, 93), (9, 70), (10, 58), (11, 96), (12, 73), (13, 54), (14, 76), (15, 56), (19, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106661) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 115) (jcc_rel32_effect_step 0x106661 4 0x115) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l1065ca [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1065ca bytes_l1065ca) (entryMap (live .l1065ca))
      38 0x1065ca bytes_l1065ca b_l1065ca := by
  have f0 : InstrSpec 0x1065ca [0x48, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x1065ca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1065ca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1065ca 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1065ca 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1065ca 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1065cf [0x4C, 0x8B, 0x6E, 0x18] (LoadPre 0x1065cf (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1065cf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1065cf 13 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x1065cf 13 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1065cf 0x4c (by decide) 5 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1065d3 [0x4C, 0x8B, 0x7E, 0x10] (LoadPre 0x1065d3 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1065d3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1065d3 15 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x1065d3 15 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1065d3 0x4c (by decide) 7 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1065d7 [0x4C, 0x8B, 0x16] (LoadPre 0x1065d7 (fun s => AddrMode.addr (.base 6 .none) s (0x1065d7 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1065d7 10 (.base 6 .none))
      [.gpr 6] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1065d7 10 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1065d7 0x4c (by decide) 2 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1065da [0x48, 0x8B, 0x5E, 0x08] (LoadPre 0x1065da (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1065da + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1065da 3 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1065da 3 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1065da 0x48 (by decide) 3 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1065de [0x89, 0xD0] (fun s => s.RIP = 0x1065de) (movR32R32Effect 0x1065de 2 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1065de 2 0 2).toInstrSpec (mov_r32_r32_effect_step 0x1065de 0xd0 (by decide)) pre_rip
  have f6 : InstrSpec 0x1065e0 [0xC0, 0xE8, 0x06] (fun s => s.RIP = 0x1065e0) (shrR8Effect 0x1065e0 3 0 6)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR8Effect_footprint 0x1065e0 3 0 6).toInstrSpec (shr_r8_imm8_effect_step 0x1065e0 0xe8 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1065e3 [0x24, 0x01] (fun s => s.RIP = 0x1065e3) (andAlImm8Effect 0x1065e3 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x1065e3 0x1).toInstrSpec (and_al_imm8_effect_step 0x1065e3 0x1) pre_rip
  have f8 : InstrSpec 0x1065e5 [0x88, 0x44, 0x24, 0x0B] (StorePre 0x1065e5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1065e5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1065e5 4 0 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1065e5 4 0 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (mov_m8_r8_effect_step 0x1065e5 0 (by decide) (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1065e9 [0x48, 0x8D, 0x74, 0x24, 0x0B] (fun s => s.RIP = 0x1065e9) (leaR64Effect 0x1065e9 6 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1065e9 6 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (lea_r64_effect_step 0x1065e9 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1065ee [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x0B] (LoadPre 0x1065ee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1065ee + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1065ee 6 9 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x1065ee 6 9 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1065ee 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1065f4 [0x88, 0x44, 0x24, 0x0B] (StorePre 0x1065f4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1065f4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1065f4 4 0 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1065f4 4 0 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (mov_m8_r8_effect_step 0x1065f4 0 (by decide) (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1065f8 [0x44, 0x0F, 0xB6, 0x64, 0x24, 0x0B] (LoadPre 0x1065f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1065f8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1065f8 6 12 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x1065f8 6 12 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1065f8 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1065fe [0x88, 0x44, 0x24, 0x0B] (StorePre 0x1065fe 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1065fe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1065fe 4 0 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1065fe 4 0 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (mov_m8_r8_effect_step 0x1065fe 0 (by decide) (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x106602 [0x44, 0x0F, 0xB6, 0x74, 0x24, 0x0B] (LoadPre 0x106602 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x106602 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x106602 6 14 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x106602 6 14 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x106602 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x106608 [0x88, 0x44, 0x24, 0x0D] (StorePre 0x106608 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x106608 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106608 4 0 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x106608 4 0 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (mov_m8_r8_effect_step 0x106608 0 (by decide) (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x10660c [0x4C, 0x8D, 0x5C, 0x24, 0x0D] (fun s => s.RIP = 0x10660c) (leaR64Effect 0x10660c 11 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (leaR64Effect_footprint 0x10660c 11 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (lea_r64_effect_step 0x10660c 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x106611 [0x0F, 0xB6, 0x6C, 0x24, 0x0D] (LoadPre 0x106611 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x106611 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106611 5 5 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x106611 5 5 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (movzx_r32_m8_effect_step 0x106611 5 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x106616 [0x89, 0xD1] (fun s => s.RIP = 0x106616) (movR32R32Effect 0x106616 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106616 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x106616 0xd1 (by decide)) pre_rip
  have f19 : InstrSpec 0x106618 [0xC1, 0xE9, 0x07] (fun s => s.RIP = 0x106618) (shrR32Effect 0x106618 3 1 7)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x106618 3 1 7).toInstrSpec (shr_r32_imm8_effect_step 0x106618 0xe9 0x7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (4, 4), (6, 6), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065cf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (4, 4), (6, 6), (7, 7), (13, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065d3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (4, 4), (6, 6), (7, 7), (13, 54), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065d7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 2), (4, 4), (6, 6), (7, 7), (10, 58), (13, 54), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065da) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 2), (3, 60), (4, 4), (6, 6), (7, 7), (10, 58), (13, 54), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065de) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (2, 2), (3, 60), (4, 4), (6, 6), (7, 7), (10, 58), (13, 54), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065e0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (2, 2), (3, 60), (4, 4), (6, 6), (7, 7), (10, 58), (13, 54), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065e3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (2, 2), (3, 60), (4, 4), (6, 6), (7, 7), (10, 58), (13, 54), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065e5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (2, 2), (3, 60), (4, 4), (6, 6), (7, 7), (10, 58), (13, 54), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065e9) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 66), (2, 2), (3, 60), (4, 4), (7, 7), (10, 58), (13, 54), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065ee) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 66), (2, 2), (3, 60), (4, 4), (7, 7), (9, 70), (10, 58), (13, 54), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065f4) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 66), (2, 2), (3, 60), (4, 4), (7, 7), (9, 70), (10, 58), (13, 54), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065f8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 66), (2, 2), (3, 60), (4, 4), (7, 7), (9, 70), (10, 58), (12, 73), (13, 54), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065fe) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 66), (2, 2), (3, 60), (4, 4), (7, 7), (9, 70), (10, 58), (12, 73), (13, 54), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106602) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 66), (2, 2), (3, 60), (4, 4), (7, 7), (9, 70), (10, 58), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106608) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 66), (2, 2), (3, 60), (4, 4), (7, 7), (9, 70), (10, 58), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10660c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 66), (2, 2), (3, 60), (4, 4), (7, 7), (9, 70), (10, 58), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106611) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f17 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 66), (2, 2), (3, 60), (4, 4), (5, 80), (7, 7), (9, 70), (10, 58), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106616) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 66), (1, 82), (2, 2), (3, 60), (4, 4), (5, 80), (7, 7), (9, 70), (10, 58), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106618) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 66), (1, 84), (2, 2), (3, 60), (4, 4), (5, 80), (7, 7), (9, 70), (10, 58), (12, 73), (13, 54), (14, 76), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10661b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1065ca_1 code

theorem block_l1065ca [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1065ca :=
  Rest.liftedBlock (rest_l1065ca code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1065ca x hx)

theorem rest_l106667_3 [Bindings] (code : CodeMap) :
    Rest (n := 168) code lifted (codeRange 0x106667 bytes_l106667) [(0, 111), (1, 166), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 159), (9, 138), (10, 127), (11, 161), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]
      18 0x10672e bytes_l106667_3 b_l106667_3 := by
  have f60 : InstrSpec 0x10672e [0x49, 0x31, 0xC0] (fun s => s.RIP = 0x10672e) (xorR64R64Effect 0x10672e 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10672e 8 0).toInstrSpec (xor_r64_r64_effect_step 0x10672e 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x106731 [0x49, 0x21, 0xC8] (fun s => s.RIP = 0x106731) (andR64R64Effect 0x106731 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x106731 8 1).toInstrSpec (and_r64_r64_effect_step 0x106731 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x106734 [0x49, 0x31, 0xC0] (fun s => s.RIP = 0x106734) (xorR64R64Effect 0x106734 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x106734 8 0).toInstrSpec (xor_r64_r64_effect_step 0x106734 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x106737 [0x40, 0x88, 0x7C, 0x24, 0x0F] (StorePre 0x106737 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x106737 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x106737 5 7 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x106737 5 7 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_rex_effect_step 0x106737 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f64 : InstrSpec 0x10673c [0x48, 0x8D, 0x44, 0x24, 0x0F] (fun s => s.RIP = 0x10673c) (leaR64Effect 0x10673c 0 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x10673c 0 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (lea_r64_effect_step 0x10673c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x106741 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x106741 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106741 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106741 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x106741 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x106741 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f66 : InstrSpec 0x106746 [0x4C, 0x89, 0x00] (StorePre 0x106746 3 (fun s => AddrMode.addr (.base 0 .none) s (0x106746 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x106746 8 (.base 0 .none))
      [.gpr 8, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x106746 8 (.base 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x106746 0x4c (by decide) 0 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f67 : InstrSpec 0x106749 [0x4C, 0x89, 0x58, 0x08] (StorePre 0x106749 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x106749 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106749 11 (.base 0 (.d8 0x8)))
      [.gpr 11, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x106749 11 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x106749 0x4c (by decide) 3 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f68 : InstrSpec 0x10674d [0x4C, 0x89, 0x48, 0x10] (StorePre 0x10674d 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x10674d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10674d 9 (.base 0 (.d8 0x10)))
      [.gpr 9, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10674d 9 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10674d 0x4c (by decide) 1 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f69 : InstrSpec 0x106751 [0x4C, 0x89, 0x50, 0x18] (StorePre 0x106751 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x106751 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106751 10 (.base 0 (.d8 0x18)))
      [.gpr 10, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x106751 10 (.base 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x106751 0x4c (by decide) 2 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f70 : InstrSpec 0x106755 [0x48, 0x83, 0xC4, 0x18] (fun s => s.RIP = 0x106755) (addR64Imm8Effect 0x106755 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x106755 4 0x18).toInstrSpec (add_r64_imm8_effect_step 0x106755 0x48 0xc4 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x106759 [0x5B] (PopPre 0x106759) (popR64Effect 0x106759 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106759 1 3).toInstrSpec (pop_r64_effect_step 0x106759 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f72 : InstrSpec 0x10675a [0x41, 0x5C] (PopPre 0x10675a) (popR64Effect 0x10675a 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10675a 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10675a 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f73 : InstrSpec 0x10675c [0x41, 0x5D] (PopPre 0x10675c) (popR64Effect 0x10675c 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10675c 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10675c 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f74 : InstrSpec 0x10675e [0x41, 0x5E] (PopPre 0x10675e) (popR64Effect 0x10675e 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10675e 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10675e 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f75 : InstrSpec 0x106760 [0x41, 0x5F] (PopPre 0x106760) (popR64Effect 0x106760 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106760 2 15).toInstrSpec (pop_r64_rex_effect_step 0x106760 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f76 : InstrSpec 0x106762 [0x5D] (PopPre 0x106762) (popR64Effect 0x106762 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106762 1 5).toInstrSpec (pop_r64_effect_step 0x106762 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f77 : InstrSpec 0x106763 [0xC3] (RetPre 0x106763) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x106763).toInstrSpec (ret_effect_step 0x106763) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f60 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 111), (1, 166), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 168), (9, 138), (10, 127), (11, 161), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106731) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f61 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 111), (1, 166), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 170), (9, 138), (10, 127), (11, 161), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106734) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f62 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 111), (1, 166), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106737) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.exec (n := 174) (ρ' := [(0, 111), (1, 166), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10673c) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 175) (RestInside.exec (n := 175) (ρ' := [(1, 166), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106741) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 176) (RestInside.out (n := 176) f65 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 177) (ρ' := [(0, 176), (1, 166), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106746) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.exec (n := 178) (ρ' := [(0, 176), (1, 166), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106749) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 179) (RestInside.exec (n := 179) (ρ' := [(0, 176), (1, 166), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10674d) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 180) (RestInside.exec (n := 180) (ρ' := [(0, 176), (1, 166), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106751) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 181) (RestInside.exec (n := 181) (ρ' := [(0, 176), (1, 166), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106755) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f70 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 176), (1, 166), (2, 103), (4, 182), (5, 81), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106759) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f71 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 185) f71 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 186) (ρ' := [(0, 176), (1, 166), (2, 103), (3, 184), (4, 185), (5, 81), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10675a) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f72 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 188) f72 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 189) (ρ' := [(0, 176), (1, 166), (2, 103), (3, 184), (4, 188), (5, 81), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 187), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10675c) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 190) (RestInside.out (n := 190) f73 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 191) f73 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 192) (ρ' := [(0, 176), (1, 166), (2, 103), (3, 184), (4, 191), (5, 81), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 187), (13, 190), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10675e) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f74 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 194) f74 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 195) (ρ' := [(0, 176), (1, 166), (2, 103), (3, 184), (4, 194), (5, 81), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 187), (13, 190), (14, 193), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106760) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 196) (RestInside.out (n := 196) f75 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 197) f75 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 198) (ρ' := [(0, 176), (1, 166), (2, 103), (3, 184), (4, 197), (5, 81), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 187), (13, 190), (14, 193), (15, 196), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106762) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f76 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 200) f76 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 201) (ρ' := [(0, 176), (1, 166), (2, 103), (3, 184), (4, 200), (5, 199), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 187), (13, 190), (14, 193), (15, 196), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106763) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f77 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 203) f77 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 204) (ρ' := [(0, 176), (1, 166), (2, 103), (3, 184), (4, 203), (5, 199), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 187), (13, 190), (14, 193), (15, 196), (22, 22), (39, 39), (50, 50), (51, 51)]) f77 (by decide) rfl rfl rfl (by decide)

theorem rest_l106667_2 [Bindings] (code : CodeMap) :
    Rest (n := 130) code lifted (codeRange 0x106667 bytes_l106667) [(0, 111), (1, 107), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 121), (10, 127), (11, 59), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]
      38 0x1066e8 bytes_l106667_2 b_l106667_2 := by
  have f40 : InstrSpec 0x1066e8 [0x0F, 0xB6, 0x4C, 0x24, 0x0C] (LoadPre 0x1066e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1066e8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1066e8 5 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1066e8 5 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x1066e8 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x1066ed [0x48, 0xF7, 0xD9] (fun s => s.RIP = 0x1066ed) (negR64Effect 0x1066ed 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR64Effect_footprint 0x1066ed 1).toInstrSpec (neg_r64_effect_step 0x1066ed 0x48 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x1066f0 [0x4D, 0x31, 0xC1] (fun s => s.RIP = 0x1066f0) (xorR64R64Effect 0x1066f0 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1066f0 9 8).toInstrSpec (xor_r64_r64_effect_step 0x1066f0 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x1066f3 [0x49, 0x21, 0xC9] (fun s => s.RIP = 0x1066f3) (andR64R64Effect 0x1066f3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1066f3 9 1).toInstrSpec (and_r64_r64_effect_step 0x1066f3 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x1066f6 [0x4D, 0x31, 0xC1] (fun s => s.RIP = 0x1066f6) (xorR64R64Effect 0x1066f6 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1066f6 9 8).toInstrSpec (xor_r64_r64_effect_step 0x1066f6 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x1066f9 [0x49, 0x89, 0xF3] (fun s => s.RIP = 0x1066f9) (movR64R64Effect 0x1066f9 11 6)
      [.gpr 6] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x1066f9 11 6).toInstrSpec (mov_r64_r64_effect_step 0x1066f9 0x49 0xf3 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x1066fc [0x89, 0xD1] (fun s => s.RIP = 0x1066fc) (movR32R32Effect 0x1066fc 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1066fc 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x1066fc 0xd1 (by decide)) pre_rip
  have f47 : InstrSpec 0x1066fe [0x4D, 0x0F, 0xAD, 0xC3] (fun s => s.RIP = 0x1066fe) (shrdR64R64ClEffect 0x1066fe 4 11 8)
      [.gpr 11, .gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrdR64R64ClEffect_footprint 0x1066fe 4 11 8).toInstrSpec (shrd_r64_r64_cl_effect_step 0x1066fe 0x4d (by decide) 0xc3 (by decide)) pre_rip
  have f48 : InstrSpec 0x106702 [0x40, 0x88, 0x7C, 0x24, 0x0C] (StorePre 0x106702 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106702 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x106702 5 7 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x106702 5 7 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m8_r8_rex_effect_step 0x106702 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x106707 [0x0F, 0xB6, 0x4C, 0x24, 0x0C] (LoadPre 0x106707 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106707 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106707 5 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x106707 5 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x106707 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f50 : InstrSpec 0x10670c [0x48, 0xF7, 0xD9] (fun s => s.RIP = 0x10670c) (negR64Effect 0x10670c 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR64Effect_footprint 0x10670c 1).toInstrSpec (neg_r64_effect_step 0x10670c 0x48 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x10670f [0x49, 0x31, 0xF3] (fun s => s.RIP = 0x10670f) (xorR64R64Effect 0x10670f 11 6)
      [.gpr 11, .gpr 6] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10670f 11 6).toInstrSpec (xor_r64_r64_effect_step 0x10670f 0x49 0xf3 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x106712 [0x49, 0x21, 0xCB] (fun s => s.RIP = 0x106712) (andR64R64Effect 0x106712 11 1)
      [.gpr 11, .gpr 1] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x106712 11 1).toInstrSpec (and_r64_r64_effect_step 0x106712 0x49 0xcb (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x106715 [0x49, 0x89, 0xC0] (fun s => s.RIP = 0x106715) (movR64R64Effect 0x106715 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x106715 8 0).toInstrSpec (mov_r64_r64_effect_step 0x106715 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x106718 [0x89, 0xD1] (fun s => s.RIP = 0x106718) (movR32R32Effect 0x106718 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106718 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x106718 0xd1 (by decide)) pre_rip
  have f55 : InstrSpec 0x10671a [0x49, 0x0F, 0xAD, 0xF0] (fun s => s.RIP = 0x10671a) (shrdR64R64ClEffect 0x10671a 4 8 6)
      [.gpr 8, .gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrdR64R64ClEffect_footprint 0x10671a 4 8 6).toInstrSpec (shrd_r64_r64_cl_effect_step 0x10671a 0x49 (by decide) 0xf0 (by decide)) pre_rip
  have f56 : InstrSpec 0x10671e [0x49, 0x31, 0xF3] (fun s => s.RIP = 0x10671e) (xorR64R64Effect 0x10671e 11 6)
      [.gpr 11, .gpr 6] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10671e 11 6).toInstrSpec (xor_r64_r64_effect_step 0x10671e 0x49 0xf3 (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x106721 [0x40, 0x88, 0x7C, 0x24, 0x0C] (StorePre 0x106721 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106721 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x106721 5 7 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x106721 5 7 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m8_r8_rex_effect_step 0x106721 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f58 : InstrSpec 0x106726 [0x0F, 0xB6, 0x4C, 0x24, 0x0C] (LoadPre 0x106726 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106726 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106726 5 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x106726 5 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x106726 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f59 : InstrSpec 0x10672b [0x48, 0xF7, 0xD9] (fun s => s.RIP = 0x10672b) (negR64Effect 0x10672b 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR64Effect_footprint 0x10672b 1).toInstrSpec (neg_r64_effect_step 0x10672b 0x48 0xd9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f40 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 111), (1, 130), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 121), (10, 127), (11, 59), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066ed) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f41 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 111), (1, 132), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 121), (10, 127), (11, 59), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066f0) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f42 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 111), (1, 132), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 134), (10, 127), (11, 59), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066f3) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f43 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 111), (1, 132), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 136), (10, 127), (11, 59), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066f6) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f44 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 111), (1, 132), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 138), (10, 127), (11, 59), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066f9) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f45 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 111), (1, 132), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 138), (10, 127), (11, 140), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066fc) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 111), (1, 142), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 138), (10, 127), (11, 140), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066fe) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f47 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 111), (1, 142), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 138), (10, 127), (11, 144), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106702) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.exec (n := 146) (ρ' := [(0, 111), (1, 142), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 138), (10, 127), (11, 144), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106707) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f49 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 111), (1, 147), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 138), (10, 127), (11, 144), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10670c) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f50 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 111), (1, 149), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 138), (10, 127), (11, 144), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10670f) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f51 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 111), (1, 149), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 138), (10, 127), (11, 151), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106712) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f52 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 111), (1, 149), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 138), (10, 127), (11, 153), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106715) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f53 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 111), (1, 149), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 155), (9, 138), (10, 127), (11, 153), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106718) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f54 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 111), (1, 157), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 155), (9, 138), (10, 127), (11, 153), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10671a) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f55 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 111), (1, 157), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 159), (9, 138), (10, 127), (11, 153), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10671e) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f56 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 111), (1, 157), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 159), (9, 138), (10, 127), (11, 161), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106721) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.exec (n := 163) (ρ' := [(0, 111), (1, 157), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 159), (9, 138), (10, 127), (11, 161), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106726) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f58 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 111), (1, 164), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 159), (9, 138), (10, 127), (11, 161), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10672b) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f59 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 111), (1, 166), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 159), (9, 138), (10, 127), (11, 161), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10672e) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l106667_3 code

theorem rest_l106667_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x106667 bytes_l106667) [(0, 0), (2, 2), (3, 89), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 91), (10, 10), (11, 59), (12, 79), (13, 63), (14, 69), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]
      58 0x1066a3 bytes_l106667_1 b_l106667_1 := by
  have f20 : InstrSpec 0x1066a3 [0x49, 0x21, 0xD9] (fun s => s.RIP = 0x1066a3) (andR64R64Effect 0x1066a3 9 3)
      [.gpr 9, .gpr 3] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1066a3 9 3).toInstrSpec (and_r64_r64_effect_step 0x1066a3 0x49 0xd9 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x1066a6 [0x4D, 0x31, 0xD1] (fun s => s.RIP = 0x1066a6) (xorR64R64Effect 0x1066a6 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1066a6 9 10).toInstrSpec (xor_r64_r64_effect_step 0x1066a6 0x4d 0xd1 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x1066a9 [0x4D, 0x31, 0xCE] (fun s => s.RIP = 0x1066a9) (xorR64R64Effect 0x1066a9 14 9)
      [.gpr 14, .gpr 9] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1066a9 14 9).toInstrSpec (xor_r64_r64_effect_step 0x1066a9 0x4d 0xce (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x1066ac [0x48, 0xF7, 0xD8] (fun s => s.RIP = 0x1066ac) (negR64Effect 0x1066ac 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR64Effect_footprint 0x1066ac 0).toInstrSpec (neg_r64_effect_step 0x1066ac 0x48 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x1066af [0x4C, 0x21, 0xF0] (fun s => s.RIP = 0x1066af) (andR64R64Effect 0x1066af 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1066af 0 14).toInstrSpec (and_r64_r64_effect_step 0x1066af 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x1066b2 [0x80, 0xF2, 0x01] (fun s => s.RIP = 0x1066b2) (xorR8Imm8Effect 0x1066b2 3 2 0x1)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR8Imm8Effect_footprint 0x1066b2 3 2 0x1).toInstrSpec (xor_r8_imm8_effect_step 0x1066b2 0xf2 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x1066b5 [0x4D, 0x89, 0xDA] (fun s => s.RIP = 0x1066b5) (movR64R64Effect 0x1066b5 10 11)
      [.gpr 11] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1066b5 10 11).toInstrSpec (mov_r64_r64_effect_step 0x1066b5 0x4d 0xda (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x1066b8 [0x89, 0xD1] (fun s => s.RIP = 0x1066b8) (movR32R32Effect 0x1066b8 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1066b8 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x1066b8 0xd1 (by decide)) pre_rip
  have f28 : InstrSpec 0x1066ba [0x49, 0xD3, 0xEA] (fun s => s.RIP = 0x1066ba) (shrR64ClEffect 0x1066ba 3 10)
      [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x1066ba 3 10).toInstrSpec (shr_r64_cl_effect_step 0x1066ba 0x49 0xea (by decide) (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x1066bd [0x4C, 0x31, 0xC8] (fun s => s.RIP = 0x1066bd) (xorR64R64Effect 0x1066bd 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1066bd 0 9).toInstrSpec (xor_r64_r64_effect_step 0x1066bd 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x1066c0 [0x40, 0x88, 0x7C, 0x24, 0x0C] (StorePre 0x1066c0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1066c0 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1066c0 5 7 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1066c0 5 7 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1066c0 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x1066c5 [0x48, 0x8D, 0x5C, 0x24, 0x0C] (fun s => s.RIP = 0x1066c5) (leaR64Effect 0x1066c5 3 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x1066c5 3 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (lea_r64_effect_step 0x1066c5 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x1066ca [0x44, 0x0F, 0xB6, 0x74, 0x24, 0x0C] (LoadPre 0x1066ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1066ca + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1066ca 6 14 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x1066ca 6 14 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1066ca 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x1066d0 [0x49, 0xF7, 0xDE] (fun s => s.RIP = 0x1066d0) (negR64Effect 0x1066d0 14)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (negR64Effect_footprint 0x1066d0 14).toInstrSpec (neg_r64_effect_step 0x1066d0 0x49 0xde (by decide) (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x1066d3 [0x4D, 0x89, 0xC1] (fun s => s.RIP = 0x1066d3) (movR64R64Effect 0x1066d3 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x1066d3 9 8).toInstrSpec (mov_r64_r64_effect_step 0x1066d3 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x1066d6 [0x4D, 0x0F, 0xAD, 0xD9] (fun s => s.RIP = 0x1066d6) (shrdR64R64ClEffect 0x1066d6 4 9 11)
      [.gpr 9, .gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrdR64R64ClEffect_footprint 0x1066d6 4 9 11).toInstrSpec (shrd_r64_r64_cl_effect_step 0x1066d6 0x4d (by decide) 0xd9 (by decide)) pre_rip
  have f36 : InstrSpec 0x1066da [0x4D, 0x31, 0xDA] (fun s => s.RIP = 0x1066da) (xorR64R64Effect 0x1066da 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1066da 10 11).toInstrSpec (xor_r64_r64_effect_step 0x1066da 0x4d 0xda (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x1066dd [0x4D, 0x21, 0xF2] (fun s => s.RIP = 0x1066dd) (andR64R64Effect 0x1066dd 10 14)
      [.gpr 10, .gpr 14] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1066dd 10 14).toInstrSpec (and_r64_r64_effect_step 0x1066dd 0x4d 0xf2 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x1066e0 [0x4D, 0x31, 0xDA] (fun s => s.RIP = 0x1066e0) (xorR64R64Effect 0x1066e0 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1066e0 10 11).toInstrSpec (xor_r64_r64_effect_step 0x1066e0 0x4d 0xda (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x1066e3 [0x40, 0x88, 0x7C, 0x24, 0x0C] (StorePre 0x1066e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1066e3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1066e3 5 7 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1066e3 5 7 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1066e3 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 0), (2, 2), (3, 89), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 93), (10, 10), (11, 59), (12, 79), (13, 63), (14, 69), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066a6) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 0), (2, 2), (3, 89), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 95), (10, 10), (11, 59), (12, 79), (13, 63), (14, 69), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066a9) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 0), (2, 2), (3, 89), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 95), (10, 10), (11, 59), (12, 79), (13, 63), (14, 97), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066ac) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 99), (2, 2), (3, 89), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 95), (10, 10), (11, 59), (12, 79), (13, 63), (14, 97), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066af) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 101), (2, 2), (3, 89), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 95), (10, 10), (11, 59), (12, 79), (13, 63), (14, 97), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066b2) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 101), (2, 103), (3, 89), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 95), (10, 10), (11, 59), (12, 79), (13, 63), (14, 97), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066b5) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 101), (2, 103), (3, 89), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 95), (10, 105), (11, 59), (12, 79), (13, 63), (14, 97), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066b8) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 101), (1, 107), (2, 103), (3, 89), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 95), (10, 105), (11, 59), (12, 79), (13, 63), (14, 97), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066ba) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 101), (1, 107), (2, 103), (3, 89), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 95), (10, 109), (11, 59), (12, 79), (13, 63), (14, 97), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066bd) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 111), (1, 107), (2, 103), (3, 89), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 95), (10, 109), (11, 59), (12, 79), (13, 63), (14, 97), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066c0) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.exec (n := 113) (ρ' := [(0, 111), (1, 107), (2, 103), (3, 89), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 95), (10, 109), (11, 59), (12, 79), (13, 63), (14, 97), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066c5) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 114) (RestInside.exec (n := 114) (ρ' := [(0, 111), (1, 107), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 95), (10, 109), (11, 59), (12, 79), (13, 63), (14, 97), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066ca) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f32 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 111), (1, 107), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 95), (10, 109), (11, 59), (12, 79), (13, 63), (14, 115), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066d0) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f33 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 111), (1, 107), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 95), (10, 109), (11, 59), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066d3) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f34 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 111), (1, 107), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 119), (10, 109), (11, 59), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066d6) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f35 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 111), (1, 107), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 121), (10, 109), (11, 59), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066da) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f36 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 111), (1, 107), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 121), (10, 123), (11, 59), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066dd) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f37 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 111), (1, 107), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 121), (10, 125), (11, 59), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066e0) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f38 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 111), (1, 107), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 121), (10, 127), (11, 59), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066e3) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.exec (n := 129) (ρ' := [(0, 111), (1, 107), (2, 103), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 121), (10, 127), (11, 59), (12, 79), (13, 63), (14, 117), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066e8) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l106667_2 code

theorem rest_l106667 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106667 bytes_l106667) (entryMap (live .l106667))
      78 0x106667 bytes_l106667 b_l106667 := by
  have f0 : InstrSpec 0x106667 [0x49, 0xFF, 0xCB] (fun s => s.RIP = 0x106667) (decR64Effect 0x106667 11)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (decR64Effect_footprint 0x106667 11).toInstrSpec (dec_r64_effect_step 0x106667 0x49 0xcb (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10666a [0x48, 0xFF, 0xCD] (fun s => s.RIP = 0x10666a) (decR64Effect 0x10666a 5)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (decR64Effect_footprint 0x10666a 5).toInstrSpec (dec_r64_effect_step 0x10666a 0x48 0xcd (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10666d [0x4C, 0x21, 0xED] (fun s => s.RIP = 0x10666d) (andR64R64Effect 0x10666d 5 13)
      [.gpr 5, .gpr 13] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10666d 5 13).toInstrSpec (and_r64_r64_effect_step 0x10666d 0x4c 0xed (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x106670 [0x49, 0x21, 0xEB] (fun s => s.RIP = 0x106670) (andR64R64Effect 0x106670 11 5)
      [.gpr 11, .gpr 5] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x106670 11 5).toInstrSpec (and_r64_r64_effect_step 0x106670 0x49 0xeb (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x106673 [0x49, 0xFF, 0xC8] (fun s => s.RIP = 0x106673) (decR64Effect 0x106673 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (decR64Effect_footprint 0x106673 8).toInstrSpec (dec_r64_effect_step 0x106673 0x49 0xc8 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x106676 [0x4D, 0x31, 0xFD] (fun s => s.RIP = 0x106676) (xorR64R64Effect 0x106676 13 15)
      [.gpr 13, .gpr 15] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x106676 13 15).toInstrSpec (xor_r64_r64_effect_step 0x106676 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x106679 [0x49, 0xF7, 0xDE] (fun s => s.RIP = 0x106679) (negR64Effect 0x106679 14)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (negR64Effect_footprint 0x106679 14).toInstrSpec (neg_r64_effect_step 0x106679 0x49 0xde (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10667c [0x4D, 0x21, 0xEE] (fun s => s.RIP = 0x10667c) (andR64R64Effect 0x10667c 14 13)
      [.gpr 14, .gpr 13] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10667c 14 13).toInstrSpec (and_r64_r64_effect_step 0x10667c 0x4d 0xee (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10667f [0x4D, 0x31, 0xFE] (fun s => s.RIP = 0x10667f) (xorR64R64Effect 0x10667f 14 15)
      [.gpr 14, .gpr 15] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10667f 14 15).toInstrSpec (xor_r64_r64_effect_step 0x10667f 0x4d 0xfe (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x106682 [0x4D, 0x21, 0xF0] (fun s => s.RIP = 0x106682) (andR64R64Effect 0x106682 8 14)
      [.gpr 8, .gpr 14] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x106682 8 14).toInstrSpec (and_r64_r64_effect_step 0x106682 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x106685 [0x49, 0x31, 0xDF] (fun s => s.RIP = 0x106685) (xorR64R64Effect 0x106685 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x106685 15 3).toInstrSpec (xor_r64_r64_effect_step 0x106685 0x49 0xdf (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x106688 [0x49, 0xF7, 0xDC] (fun s => s.RIP = 0x106688) (negR64Effect 0x106688 12)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (negR64Effect_footprint 0x106688 12).toInstrSpec (neg_r64_effect_step 0x106688 0x49 0xdc (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10668b [0x4D, 0x21, 0xFC] (fun s => s.RIP = 0x10668b) (andR64R64Effect 0x10668b 12 15)
      [.gpr 12, .gpr 15] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10668b 12 15).toInstrSpec (and_r64_r64_effect_step 0x10668b 0x4d 0xfc (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10668e [0x49, 0x31, 0xDC] (fun s => s.RIP = 0x10668e) (xorR64R64Effect 0x10668e 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10668e 12 3).toInstrSpec (xor_r64_r64_effect_step 0x10668e 0x49 0xdc (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x106691 [0x4C, 0x31, 0xE5] (fun s => s.RIP = 0x106691) (xorR64R64Effect 0x106691 5 12)
      [.gpr 5, .gpr 12] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x106691 5 12).toInstrSpec (xor_r64_r64_effect_step 0x106691 0x4c 0xe5 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x106694 [0x48, 0xF7, 0xDE] (fun s => s.RIP = 0x106694) (negR64Effect 0x106694 6)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (negR64Effect_footprint 0x106694 6).toInstrSpec (neg_r64_effect_step 0x106694 0x48 0xde (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x106697 [0x48, 0x21, 0xEE] (fun s => s.RIP = 0x106697) (andR64R64Effect 0x106697 6 5)
      [.gpr 6, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x106697 6 5).toInstrSpec (and_r64_r64_effect_step 0x106697 0x48 0xee (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10669a [0x4C, 0x31, 0xE6] (fun s => s.RIP = 0x10669a) (xorR64R64Effect 0x10669a 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10669a 6 12).toInstrSpec (xor_r64_r64_effect_step 0x10669a 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10669d [0x4C, 0x31, 0xD3] (fun s => s.RIP = 0x10669d) (xorR64R64Effect 0x10669d 3 10)
      [.gpr 3, .gpr 10] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10669d 3 10).toInstrSpec (xor_r64_r64_effect_step 0x10669d 0x4c 0xd3 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1066a0 [0x49, 0xF7, 0xD9] (fun s => s.RIP = 0x1066a0) (negR64Effect 0x1066a0 9)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (negR64Effect_footprint 0x1066a0 9).toInstrSpec (neg_r64_effect_step 0x1066a0 0x49 0xd9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10666a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10666d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106670) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106673) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 61), (9, 9), (10, 10), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106676) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 61), (9, 9), (10, 10), (11, 59), (12, 12), (13, 63), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106679) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 61), (9, 9), (10, 10), (11, 59), (12, 12), (13, 63), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10667c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 61), (9, 9), (10, 10), (11, 59), (12, 12), (13, 63), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10667f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 61), (9, 9), (10, 10), (11, 59), (12, 12), (13, 63), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106682) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 71), (9, 9), (10, 10), (11, 59), (12, 12), (13, 63), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106685) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 71), (9, 9), (10, 10), (11, 59), (12, 12), (13, 63), (14, 69), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106688) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 71), (9, 9), (10, 10), (11, 59), (12, 75), (13, 63), (14, 69), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10668b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 71), (9, 9), (10, 10), (11, 59), (12, 77), (13, 63), (14, 69), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10668e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 71), (9, 9), (10, 10), (11, 59), (12, 79), (13, 63), (14, 69), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106691) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 81), (6, 6), (7, 7), (8, 71), (9, 9), (10, 10), (11, 59), (12, 79), (13, 63), (14, 69), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106694) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 81), (6, 83), (7, 7), (8, 71), (9, 9), (10, 10), (11, 59), (12, 79), (13, 63), (14, 69), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106697) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 81), (6, 85), (7, 7), (8, 71), (9, 9), (10, 10), (11, 59), (12, 79), (13, 63), (14, 69), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10669a) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 9), (10, 10), (11, 59), (12, 79), (13, 63), (14, 69), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10669d) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (2, 2), (3, 89), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 9), (10, 10), (11, 59), (12, 79), (13, 63), (14, 69), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066a0) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (2, 2), (3, 89), (4, 4), (5, 81), (6, 87), (7, 7), (8, 71), (9, 91), (10, 10), (11, 59), (12, 79), (13, 63), (14, 69), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066a3) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l106667_1 code

theorem block_l106667 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106667 :=
  Rest.liftedBlock (rest_l106667 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106667 x hx)

theorem rest_l106764 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106764 bytes_l106764) (entryMap (live .l106764))
      4 0x106764 bytes_l106764 b_l106764 := by
  have f0 : InstrSpec 0x106764 [0xBE, 0x37, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106764) (movR32Imm32Effect 0x106764 5 6 0x37)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x106764 5 6 0x37).toInstrSpec (mov_r32_imm32_effect_step 0x106764 0xbe (by decide) 0x37) pre_rip
  have f1 : InstrSpec 0x106769 [0x48, 0xC7, 0xC7, 0x9C, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x106769) (movR64Imm32Effect 0x106769 7 0x20249c)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x106769 7 0x20249c).toInstrSpec (mov_r64_imm32_effect_step 0x106769 0x48 0xc7 (by decide) (by decide) (by decide) 0x20249c) pre_rip
  have f2 : InstrSpec 0x106770 [0x48, 0xC7, 0xC2, 0xB8, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x106770) (movR64Imm32Effect 0x106770 2 0x2024b8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x106770 2 0x2024b8).toInstrSpec (mov_r64_imm32_effect_step 0x106770 0x48 0xc2 (by decide) (by decide) (by decide) 0x2024b8) pre_rip
  have f3 : InstrSpec 0x106777 [0xE8, 0xF4, 0x2F, 0x02, 0x00] (PushPre 0x106777 5) (callEffect (fun _ => 0x129770) 0x10677c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106777 0x129770 0x10677c).toInstrSpec (call_rel32_effect_step 0x106777 0x22ff4 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 53)]) (p' := 0x106769) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x106770) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x106777) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)]) (p' := 0x129770) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l106764 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106764 :=
  Rest.liftedBlock (rest_l106764 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106764 x hx)

theorem rest_l10677c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10677c bytes_l10677c) (entryMap (live .l10677c))
      4 0x10677c bytes_l10677c b_l10677c := by
  have f0 : InstrSpec 0x10677c [0xBE, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10677c) (movR32Imm32Effect 0x10677c 5 6 0x10)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10677c 5 6 0x10).toInstrSpec (mov_r32_imm32_effect_step 0x10677c 0xbe (by decide) 0x10) pre_rip
  have f1 : InstrSpec 0x106781 [0x48, 0xC7, 0xC7, 0xD0, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x106781) (movR64Imm32Effect 0x106781 7 0x2024d0)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x106781 7 0x2024d0).toInstrSpec (mov_r64_imm32_effect_step 0x106781 0x48 0xc7 (by decide) (by decide) (by decide) 0x2024d0) pre_rip
  have f2 : InstrSpec 0x106788 [0x48, 0xC7, 0xC2, 0x00, 0x25, 0x20, 0x00] (fun s => s.RIP = 0x106788) (movR64Imm32Effect 0x106788 2 0x202500)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x106788 2 0x202500).toInstrSpec (mov_r64_imm32_effect_step 0x106788 0x48 0xc2 (by decide) (by decide) (by decide) 0x202500) pre_rip
  have f3 : InstrSpec 0x10678f [0xE8, 0xCC, 0x2D, 0x02, 0x00] (PushPre 0x10678f 5) (callEffect (fun _ => 0x129560) 0x106794)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10678f 0x129560 0x106794).toInstrSpec (call_rel32_effect_step 0x10678f 0x22dcc (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 53)]) (p' := 0x106781) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x106788) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x10678f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)]) (p' := 0x129560) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10677c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10677c :=
  Rest.liftedBlock (rest_l10677c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10677c x hx)

theorem rest_l106794 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106794 bytes_l106794) (entryMap (live .l106794))
      4 0x106794 bytes_l106794 b_l106794 := by
  have f0 : InstrSpec 0x106794 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106794) (fun _ => nopEffect 0x106794 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x106794 10).toInstrSpec (nop_m_effect_step 0x106794 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10679e [0x66, 0x90] (fun s => s.RIP = 0x10679e) (fun _ => nopEffect 0x10679e 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10679e 2).toInstrSpec (nop_66_effect_step 0x10679e) pre_rip
  have f2 : InstrSpec 0x1067a0 [0x48, 0x8B, 0x3F] (LoadPre 0x1067a0 (fun s => AddrMode.addr (.base 7 .none) s (0x1067a0 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1067a0 7 (.base 7 .none))
      [.gpr 7] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1067a0 7 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1067a0 0x48 (by decide) 7 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x10679e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x1067a0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (14, 14), (15, 15)]) (p' := 0x1067a3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel32_effect_step 0x1067a3 0x21528 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l106794 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106794 :=
  Rest.liftedBlock (rest_l106794 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106794 x hx)

theorem rest_l127cd0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127cd0 bytes_l127cd0) (entryMap (live .l127cd0))
      9 0x127cd0 bytes_l127cd0 b_l127cd0 := by
  have f0 : InstrSpec 0x127cd0 [0x41, 0x56] (PushPre 0x127cd0 2) (pushR64Effect 0x127cd0 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x127cd0 2 14).toInstrSpec (push_r64_rex_effect_step 0x127cd0 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x127cd2 [0x53] (PushPre 0x127cd2 1) (pushR64Effect 0x127cd2 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x127cd2 1 3).toInstrSpec (push_r64_effect_step 0x127cd2 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x127cd3 [0x48, 0x83, 0xEC, 0x18] (fun s => s.RIP = 0x127cd3) (subR64Imm8Effect 0x127cd3 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x127cd3 4 0x18).toInstrSpec (sub_r64_imm8_effect_step 0x127cd3 0x48 0xec 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x127cd7 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x127cd7) (movR64R64Effect 0x127cd7 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x127cd7 3 7).toInstrSpec (mov_r64_r64_effect_step 0x127cd7 0x48 0xfb (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127cda [0x49, 0x89, 0xE6] (fun s => s.RIP = 0x127cda) (movR64R64Effect 0x127cda 14 4)
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x127cda 14 4).toInstrSpec (mov_r64_r64_effect_step 0x127cda 0x49 0xe6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x127cdd [0xB9, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127cdd) (movR32Imm32Effect 0x127cdd 5 1 0x6)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x127cdd 5 1 0x6).toInstrSpec (mov_r32_imm32_effect_step 0x127cdd 0xb9 (by decide) 0x6) pre_rip
  have f6 : InstrSpec 0x127ce2 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x127ce2) (movR64R64Effect 0x127ce2 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x127ce2 7 14).toInstrSpec (mov_r64_r64_effect_step 0x127ce2 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x127ce5 [0x48, 0xC7, 0xC2, 0xA5, 0x39, 0x20, 0x00] (fun s => s.RIP = 0x127ce5) (movR64Imm32Effect 0x127ce5 2 0x2039a5)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x127ce5 2 0x2039a5).toInstrSpec (mov_r64_imm32_effect_step 0x127ce5 0x48 0xc2 (by decide) (by decide) (by decide) 0x2039a5) pre_rip
  have f8 : InstrSpec 0x127cec [0xE8, 0xDF, 0x0D, 0x00, 0x00] (PushPre 0x127cec 5) (callEffect (fun _ => 0x128ad0) 0x127cf1)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x127cec 0x128ad0 0x127cf1).toInstrSpec (call_rel32_effect_step 0x127cec 0xddf (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x127cd2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x127cd3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x127cd7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x127cda) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (14, 61), (15, 15)]) (p' := 0x127cdd) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (14, 61), (15, 15)]) (p' := 0x127ce2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 63), (3, 59), (4, 57), (5, 5), (6, 6), (7, 65), (14, 61), (15, 15)]) (p' := 0x127ce5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 63), (2, 67), (3, 59), (4, 57), (5, 5), (6, 6), (7, 65), (14, 61), (15, 15)]) (p' := 0x127cec) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 63), (2, 67), (3, 59), (4, 69), (5, 5), (6, 6), (7, 65), (14, 61), (15, 15)]) (p' := 0x128ad0) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l127cd0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127cd0 :=
  Rest.liftedBlock (rest_l127cd0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127cd0 x hx)

theorem rest_l127cf1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127cf1 bytes_l127cf1) (entryMap (live .l127cf1))
      4 0x127cf1 bytes_l127cf1 b_l127cf1 := by
  have f0 : InstrSpec 0x127cf1 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x127cf1) (movR64R64Effect 0x127cf1 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x127cf1 7 14).toInstrSpec (mov_r64_r64_effect_step 0x127cf1 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127cf4 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x127cf4) (movR64R64Effect 0x127cf4 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x127cf4 6 3).toInstrSpec (mov_r64_r64_effect_step 0x127cf4 0x48 0xde (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127cf7 [0x48, 0xC7, 0xC2, 0xB0, 0x39, 0x20, 0x00] (fun s => s.RIP = 0x127cf7) (movR64Imm32Effect 0x127cf7 2 0x2039b0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x127cf7 2 0x2039b0).toInstrSpec (mov_r64_imm32_effect_step 0x127cf7 0x48 0xc2 (by decide) (by decide) (by decide) 0x2039b0) pre_rip
  have f3 : InstrSpec 0x127cfe [0xE8, 0x0D, 0x0C, 0x00, 0x00] (PushPre 0x127cfe 5) (callEffect (fun _ => 0x128910) 0x127d03)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x127cfe 0x128910 0x127d03).toInstrSpec (call_rel32_effect_step 0x127cfe 0xc0d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127cf4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127cf7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127cfe) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128910) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l127cf1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127cf1 :=
  Rest.liftedBlock (rest_l127cf1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127cf1 x hx)

theorem rest_l127d03 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127d03 bytes_l127d03) (entryMap (live .l127d03))
      2 0x127d03 bytes_l127d03 b_l127d03 := by
  have f0 : InstrSpec 0x127d03 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x127d03) (movR64R64Effect 0x127d03 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x127d03 7 0).toInstrSpec (mov_r64_r64_effect_step 0x127d03 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127d06 [0xE8, 0x35, 0x0D, 0x00, 0x00] (PushPre 0x127d06 5) (callEffect (fun _ => 0x128a40) 0x127d0b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x127d06 0x128a40 0x127d0b).toInstrSpec (call_rel32_effect_step 0x127d06 0xd35 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d06) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 55), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a40) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l127d03 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127d03 :=
  Rest.liftedBlock (rest_l127d03 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127d03 x hx)

theorem rest_l127d0b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127d0b bytes_l127d0b) (entryMap (live .l127d0b))
      4 0x127d0b bytes_l127d0b b_l127d0b := by
  have f0 : InstrSpec 0x127d0b [0x48, 0x83, 0xC4, 0x18] (fun s => s.RIP = 0x127d0b) (addR64Imm8Effect 0x127d0b 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x127d0b 4 0x18).toInstrSpec (add_r64_imm8_effect_step 0x127d0b 0x48 0xc4 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127d0f [0x5B] (PopPre 0x127d0f) (popR64Effect 0x127d0f 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x127d0f 1 3).toInstrSpec (pop_r64_effect_step 0x127d0f 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x127d10 [0x41, 0x5E] (PopPre 0x127d10) (popR64Effect 0x127d10 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x127d10 2 14).toInstrSpec (pop_r64_rex_effect_step 0x127d10 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x127d12 [0xC3] (RetPre 0x127d12) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127d12).toInstrSpec (ret_effect_step 0x127d12) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d0f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d10) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d12) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f3 (by decide) rfl rfl rfl (by decide)

theorem block_l127d0b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127d0b :=
  Rest.liftedBlock (rest_l127d0b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127d0b x hx)

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

theorem_by block_l1065b0_eval :
    program.runBlock (dialect code) ⟨.l1065b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1065ca_eval :
    program.runBlock (dialect code) ⟨.l1065ca, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106667_eval :
    program.runBlock (dialect code) ⟨.l106667, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106764_eval :
    program.runBlock (dialect code) ⟨.l106764, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10677c_eval :
    program.runBlock (dialect code) ⟨.l10677c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106794_eval :
    program.runBlock (dialect code) ⟨.l106794, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127cd0_eval :
    program.runBlock (dialect code) ⟨.l127cd0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127cf1_eval :
    program.runBlock (dialect code) ⟨.l127cf1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127d03_eval :
    program.runBlock (dialect code) ⟨.l127d03, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127d0b_eval :
    program.runBlock (dialect code) ⟨.l127d0b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
