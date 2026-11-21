import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1174a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1119c0 bytes_l1174a0) (entryMap (live .l1174a0))
      16 0x1119c0 bytes_l1174a0 b_l1174a0 := by
  have f0 : InstrSpec 0x1119c0 [0x48, 0x8D, 0x4C, 0x24, 0x10] (fun s => s.RIP = 0x1119c0) (leaR64Effect 0x1119c0 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x1119c0 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1119c0 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1119c5 [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x1119c5) (xorR32R32Effect 0x1119c5 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1119c5 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1119c5 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1119c8 [0x4C, 0x2B, 0x4C, 0x24, 0x10] (LoadPre 0x1119c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1119c8 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1119c8 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 9, .gpr 4] [] [.reg 9, .flags, .rip] :=
    (subR64M64Effect_footprint 0x1119c8 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (sub_r64_m64_effect_step 0x1119c8 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1119cd [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x1119cd) (movR64R64Effect 0x1119cd 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1119cd 6 3).toInstrSpec (mov_r64_r64_effect_step 0x1119cd 0x48 0xde (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1119d0 [0x4C, 0x8B, 0x44, 0x24, 0x58] (LoadPre 0x1119d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1119d0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1119d0 8 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1119d0 8 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x1119d0 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1119d5 [0x4C, 0x29, 0xC6] (fun s => s.RIP = 0x1119d5) (subR64R64Effect 0x1119d5 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1119d5 6 8).toInstrSpec (sub_r64_r64_effect_step 0x1119d5 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1119d8 [0x49, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x1119d8) (sarR64Effect 0x1119d8 4 9 63)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (sarR64Effect_footprint 0x1119d8 4 9 63).toInstrSpec (sar_r64_imm8_effect_step 0x1119d8 0x49 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1119dc [0x49, 0x01, 0xF1] (fun s => s.RIP = 0x1119dc) (addR64R64Effect 0x1119dc 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1119dc 9 6).toInstrSpec (add_r64_r64_effect_step 0x1119dc 0x49 0xf1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1119df [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x1119df) (movR64R64Effect 0x1119df 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1119df 6 3).toInstrSpec (mov_r64_r64_effect_step 0x1119df 0x48 0xde (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1119e2 [0x48, 0xF7, 0xD6] (fun s => s.RIP = 0x1119e2) (notR64Effect 0x1119e2 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR64Effect_footprint 0x1119e2 6).toInstrSpec (not_r64_effect_step 0x1119e2 0x48 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1119e5 [0x4C, 0x89, 0xC7] (fun s => s.RIP = 0x1119e5) (movR64R64Effect 0x1119e5 7 8)
      [.gpr 8] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1119e5 7 8).toInstrSpec (mov_r64_r64_effect_step 0x1119e5 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1119e8 [0x48, 0x21, 0xF7] (fun s => s.RIP = 0x1119e8) (andR64R64Effect 0x1119e8 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1119e8 7 6).toInstrSpec (and_r64_r64_effect_step 0x1119e8 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1119eb [0x4C, 0x09, 0xC6] (fun s => s.RIP = 0x1119eb) (orR64R64Effect 0x1119eb 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1119eb 6 8).toInstrSpec (or_r64_r64_effect_step 0x1119eb 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1119ee [0x4C, 0x21, 0xCE] (fun s => s.RIP = 0x1119ee) (andR64R64Effect 0x1119ee 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1119ee 6 9).toInstrSpec (and_r64_r64_effect_step 0x1119ee 0x4c 0xce (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1119f1 [0x48, 0x09, 0xFE] (fun s => s.RIP = 0x1119f1) (orR64R64Effect 0x1119f1 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1119f1 6 7).toInstrSpec (or_r64_r64_effect_step 0x1119f1 0x48 0xfe (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1119f4 [0x48, 0xC1, 0xEE, 0x3F] (fun s => s.RIP = 0x1119f4) (shrR64Effect 0x1119f4 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x1119f4 4 6 63).toInstrSpec (shr_r64_imm8_effect_step 0x1119f4 0x48 0xee 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119c5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 54), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119c8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 56), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119cd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 58), (9, 56), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119d0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 58), (8, 60), (9, 56), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119d5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 62), (8, 60), (9, 56), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119d8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 62), (8, 60), (9, 64), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119dc) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 62), (8, 60), (9, 66), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119df) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 68), (8, 60), (9, 66), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119e2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 70), (8, 60), (9, 66), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119e5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 70), (7, 72), (8, 60), (9, 66), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119e8) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 70), (7, 74), (8, 60), (9, 66), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119eb) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 76), (7, 74), (8, 60), (9, 66), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119ee) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 78), (7, 74), (8, 60), (9, 66), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119f1) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 80), (7, 74), (8, 60), (9, 66), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119f4) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 82), (7, 74), (8, 60), (9, 66), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119f8) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 84) (by decide) rfl

theorem block_l1174a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1174a0 :=
  Rest.liftedBlock (rest_l1174a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1174a0 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
