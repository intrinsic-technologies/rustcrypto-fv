import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1174d8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1119f8 bytes_l1174d8) (entryMap (live .l1174d8))
      16 0x1119f8 bytes_l1174d8 b_l1174d8 := by
  have f0 : InstrSpec 0x1119f8 [0x48, 0x89, 0x74, 0x24, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1119f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1119f8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1119f8 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1119f8 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1119f8 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1119fd [0x31, 0xF6] (fun s => s.RIP = 0x1119fd) (xorR32R32Effect 0x1119fd 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1119fd 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x1119fd 0xf6 (by decide)) pre_rip
  have f2 : InstrSpec 0x1119ff [0x48, 0x2B, 0x74, 0x24, 0x10] (LoadPre 0x1119ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1119ff + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1119ff 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (subR64M64Effect_footprint 0x1119ff 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (sub_r64_m64_effect_step 0x1119ff 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x111a04 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x111a04) (movR64R64Effect 0x111a04 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x111a04 7 12).toInstrSpec (mov_r64_r64_effect_step 0x111a04 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x111a07 [0x4C, 0x8B, 0x74, 0x24, 0x60] (LoadPre 0x111a07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x111a07 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111a07 14 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x111a07 14 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x111a07 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x111a0c [0x4C, 0x29, 0xF7] (fun s => s.RIP = 0x111a0c) (subR64R64Effect 0x111a0c 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (subR64R64Effect_footprint 0x111a0c 7 14).toInstrSpec (sub_r64_r64_effect_step 0x111a0c 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x111a0f [0x48, 0xC1, 0xFE, 0x3F] (fun s => s.RIP = 0x111a0f) (sarR64Effect 0x111a0f 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (sarR64Effect_footprint 0x111a0f 4 6 63).toInstrSpec (sar_r64_imm8_effect_step 0x111a0f 0x48 0xfe 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111a13 [0x48, 0x01, 0xFE] (fun s => s.RIP = 0x111a13) (addR64R64Effect 0x111a13 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x111a13 6 7).toInstrSpec (add_r64_r64_effect_step 0x111a13 0x48 0xfe (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111a16 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x111a16) (movR64R64Effect 0x111a16 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x111a16 7 12).toInstrSpec (mov_r64_r64_effect_step 0x111a16 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x111a19 [0x48, 0xF7, 0xD7] (fun s => s.RIP = 0x111a19) (notR64Effect 0x111a19 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (notR64Effect_footprint 0x111a19 7).toInstrSpec (not_r64_effect_step 0x111a19 0x48 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x111a1c [0x4D, 0x89, 0xF0] (fun s => s.RIP = 0x111a1c) (movR64R64Effect 0x111a1c 8 14)
      [.gpr 14] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x111a1c 8 14).toInstrSpec (mov_r64_r64_effect_step 0x111a1c 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x111a1f [0x49, 0x21, 0xF8] (fun s => s.RIP = 0x111a1f) (andR64R64Effect 0x111a1f 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111a1f 8 7).toInstrSpec (and_r64_r64_effect_step 0x111a1f 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x111a22 [0x4C, 0x09, 0xF7] (fun s => s.RIP = 0x111a22) (orR64R64Effect 0x111a22 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111a22 7 14).toInstrSpec (or_r64_r64_effect_step 0x111a22 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111a25 [0x48, 0x21, 0xF7] (fun s => s.RIP = 0x111a25) (andR64R64Effect 0x111a25 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111a25 7 6).toInstrSpec (and_r64_r64_effect_step 0x111a25 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x111a28 [0x4C, 0x09, 0xC7] (fun s => s.RIP = 0x111a28) (orR64R64Effect 0x111a28 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111a28 7 8).toInstrSpec (or_r64_r64_effect_step 0x111a28 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x111a2b [0x48, 0xC1, 0xEF, 0x3F] (fun s => s.RIP = 0x111a2b) (shrR64Effect 0x111a2b 4 7 63)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x111a2b 4 7 63).toInstrSpec (shr_r64_imm8_effect_step 0x111a2b 0x48 0xef 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119fd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119ff) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 56), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a04) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 56), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a07) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 56), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a0c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 56), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a0f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 64), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a13) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 66), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a16) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 66), (7, 68), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a19) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 66), (7, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a1c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 66), (7, 70), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a1f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 66), (7, 70), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a22) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 66), (7, 76), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a25) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 66), (7, 78), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a28) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 66), (7, 80), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a2b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 66), (7, 82), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a2f) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 84) (by decide) rfl

theorem block_l1174d8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1174d8 :=
  Rest.liftedBlock (rest_l1174d8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1174d8 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
