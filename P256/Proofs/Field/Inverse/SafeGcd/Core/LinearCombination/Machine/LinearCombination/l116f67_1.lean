import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l116f67_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x111487 bytes_l116f67) [(0, 0), (1, 88), (2, 80), (3, 90), (4, 4), (6, 86), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 76), (22, 22), (39, 39), (51, 51)]
      5 0x1114ca bytes_l116f67_1 b_l116f67_1 := by
  have f20 : InstrSpec 0x1114ca [0x48, 0x01, 0xD3] (fun s => s.RIP = 0x1114ca) (addR64R64Effect 0x1114ca 3 2)
      [.gpr 3, .gpr 2] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1114ca 3 2).toInstrSpec (add_r64_r64_effect_step 0x1114ca 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x1114cd [0x48, 0x21, 0xD9] (fun s => s.RIP = 0x1114cd) (andR64R64Effect 0x1114cd 1 3)
      [.gpr 1, .gpr 3] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1114cd 1 3).toInstrSpec (and_r64_r64_effect_step 0x1114cd 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x1114d0 [0x48, 0x09, 0xF1] (fun s => s.RIP = 0x1114d0) (orR64R64Effect 0x1114d0 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1114d0 1 6).toInstrSpec (or_r64_r64_effect_step 0x1114d0 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x1114d3 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x1114d3) (shrR64Effect 0x1114d3 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x1114d3 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x1114d3 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x1114d7 [0x48, 0x89, 0x0C, 0x24] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1114d7 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1114d7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1114d7 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1114d7 1 (.sib 4 none 0 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1114d7 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 0), (1, 88), (2, 80), (3, 92), (4, 4), (6, 86), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114cd) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 0), (1, 94), (2, 80), (3, 92), (4, 4), (6, 86), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114d0) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 0), (1, 96), (2, 80), (3, 92), (4, 4), (6, 86), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114d3) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 0), (1, 98), (2, 80), (3, 92), (4, 4), (6, 86), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114d7) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 0), (1, 98), (2, 80), (3, 92), (4, 4), (6, 86), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114db) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 101) (by decide) rfl
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
