import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l118882 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112da2 bytes_l118882) (entryMap (live .l118882))
      9 0x112da2 bytes_l118882 b_l118882 := by
  have f0 : InstrSpec 0x112da2 [0x4C, 0x89, 0x0C, 0x24] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112da2 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112da2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112da2 9 (.sib 4 none 0 .none))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112da2 9 (.sib 4 none 0 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112da2 0x4c (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x112da6 [0x49, 0x89, 0xE1] (fun s => s.RIP = 0x112da6) (movR64R64Effect 0x112da6 9 4)
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x112da6 9 4).toInstrSpec (mov_r64_r64_effect_step 0x112da6 0x49 0xe1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112da9 [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x112da9) (xorR32R32Effect 0x112da9 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x112da9 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x112da9 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x112dac [0x4C, 0x2B, 0x0C, 0x24] (LoadPre 0x112dac (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112dac + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x112dac 9 (.sib 4 none 0 .none))
      [.gpr 9, .gpr 4] [] [.reg 9, .flags, .rip] :=
    (subR64M64Effect_footprint 0x112dac 9 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x112dac 0x4c (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x112db0 [0x49, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x112db0) (sarR64Effect 0x112db0 4 9 63)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (sarR64Effect_footprint 0x112db0 4 9 63).toInstrSpec (sar_r64_imm8_effect_step 0x112db0 0x49 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x112db4 [0x49, 0x01, 0xC9] (fun s => s.RIP = 0x112db4) (addR64R64Effect 0x112db4 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112db4 9 1).toInstrSpec (add_r64_r64_effect_step 0x112db4 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x112db7 [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x112db7) (notR64Effect 0x112db7 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x112db7 1).toInstrSpec (not_r64_effect_step 0x112db7 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x112dba [0x4C, 0x21, 0xC9] (fun s => s.RIP = 0x112dba) (andR64R64Effect 0x112dba 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112dba 1 9).toInstrSpec (and_r64_r64_effect_step 0x112dba 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x112dbd [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x112dbd) (shrR64Effect 0x112dbd 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x112dbd 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x112dbd 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112da6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 54), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112da9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 56), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112dac) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 58), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112db0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 60), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112db4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112db7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 64), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112dba) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 66), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112dbd) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 68), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112dc1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 70) (by decide) rfl

theorem block_l118882 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l118882 :=
  Rest.liftedBlock (rest_l118882 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l118882 x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
