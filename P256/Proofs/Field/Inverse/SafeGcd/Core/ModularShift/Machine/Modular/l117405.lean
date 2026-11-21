import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117405 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111925 bytes_l117405) (entryMap (live .l117405))
      9 0x111925 bytes_l117405 b_l117405 := by
  have f0 : InstrSpec 0x111925 [0x83, 0xE6, 0x01] (fun s => s.RIP = 0x111925) (andR32Imm8Effect 0x111925 3 6 0x1)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x111925 3 6 0x1).toInstrSpec (and_r32_imm8_effect_step 0x111925 0xe6 0x1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x111928 [0x49, 0x89, 0xC0] (fun s => s.RIP = 0x111928) (movR64R64Effect 0x111928 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x111928 8 0).toInstrSpec (mov_r64_r64_effect_step 0x111928 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11192b [0x49, 0xF7, 0xD0] (fun s => s.RIP = 0x11192b) (notR64Effect 0x11192b 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (notR64Effect_footprint 0x11192b 8).toInstrSpec (not_r64_effect_step 0x11192b 0x49 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11192e [0x49, 0x01, 0xF0] (fun s => s.RIP = 0x11192e) (addR64R64Effect 0x11192e 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11192e 8 6).toInstrSpec (add_r64_r64_effect_step 0x11192e 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x111931 [0x49, 0x31, 0xC0] (fun s => s.RIP = 0x111931) (xorR64R64Effect 0x111931 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111931 8 0).toInstrSpec (xor_r64_r64_effect_step 0x111931 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x111934 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x10] (LoadPre 0x111934 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111934 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x111934 6 13 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x111934 6 13 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x111934 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x11193a [0x49, 0xF7, 0xDD] (fun s => s.RIP = 0x11193a) (negR64Effect 0x11193a 13)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (negR64Effect_footprint 0x11193a 13).toInstrSpec (neg_r64_effect_step 0x11193a 0x49 0xdd (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11193d [0x4D, 0x21, 0xC5] (fun s => s.RIP = 0x11193d) (andR64R64Effect 0x11193d 13 8)
      [.gpr 13, .gpr 8] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11193d 13 8).toInstrSpec (and_r64_r64_effect_step 0x11193d 0x4d 0xc5 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111940 [0x49, 0x31, 0xC5] (fun s => s.RIP = 0x111940) (xorR64R64Effect 0x111940 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111940 13 0).toInstrSpec (xor_r64_r64_effect_step 0x111940 0x49 0xc5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (7, 7), (9, 9), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111928) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (7, 7), (8, 55), (9, 9), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11192b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (7, 7), (8, 57), (9, 9), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11192e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (7, 7), (8, 59), (9, 9), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111931) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (7, 7), (8, 61), (9, 9), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111934) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (7, 7), (8, 61), (9, 9), (13, 63), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11193a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (7, 7), (8, 61), (9, 9), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11193d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (7, 7), (8, 61), (9, 9), (13, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111940) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (7, 7), (8, 61), (9, 9), (13, 69), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111943) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 71) (by decide) rfl

theorem block_l117405 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117405 :=
  Rest.liftedBlock (rest_l117405 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117405 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
