import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l11700a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11152a bytes_l11700a) (entryMap (live .l11700a))
      13 0x11152a bytes_l11700a b_l11700a := by
  have f0 : InstrSpec 0x11152a [0x88, 0x0C, 0x24] (StorePre 0x11152a 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11152a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x11152a 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11152a 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x11152a 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11152d [0x49, 0x89, 0xE7] (fun s => s.RIP = 0x11152d) (movR64R64Effect 0x11152d 15 4)
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x11152d 15 4).toInstrSpec (mov_r64_r64_effect_step 0x11152d 0x49 0xe7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x111530 [0x49, 0x31, 0xC4] (fun s => s.RIP = 0x111530) (xorR64R64Effect 0x111530 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111530 12 0).toInstrSpec (xor_r64_r64_effect_step 0x111530 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x111533 [0x0F, 0xB6, 0x34, 0x24] (LoadPre 0x111533 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111533 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x111533 4 6 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x111533 4 6 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x111533 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x111537 [0x48, 0xF7, 0xDE] (fun s => s.RIP = 0x111537) (negR64Effect 0x111537 6)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (negR64Effect_footprint 0x111537 6).toInstrSpec (neg_r64_effect_step 0x111537 0x48 0xde (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11153a [0x4C, 0x21, 0xE6] (fun s => s.RIP = 0x11153a) (andR64R64Effect 0x11153a 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11153a 6 12).toInstrSpec (and_r64_r64_effect_step 0x11153a 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11153d [0x48, 0x31, 0xC6] (fun s => s.RIP = 0x11153d) (xorR64R64Effect 0x11153d 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x11153d 6 0).toInstrSpec (xor_r64_r64_effect_step 0x11153d 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111540 [0x88, 0x0C, 0x24] (StorePre 0x111540 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111540 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x111540 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111540 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x111540 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x111543 [0x0F, 0xB6, 0x04, 0x24] (LoadPre 0x111543 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111543 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x111543 4 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x111543 4 0 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x111543 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x111547 [0x4D, 0x31, 0xC6] (fun s => s.RIP = 0x111547) (xorR64R64Effect 0x111547 14 8)
      [.gpr 14, .gpr 8] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111547 14 8).toInstrSpec (xor_r64_r64_effect_step 0x111547 0x4d 0xc6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11154a [0x48, 0xF7, 0xD8] (fun s => s.RIP = 0x11154a) (negR64Effect 0x11154a 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR64Effect_footprint 0x11154a 0).toInstrSpec (neg_r64_effect_step 0x11154a 0x48 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11154d [0x4C, 0x21, 0xF0] (fun s => s.RIP = 0x11154d) (andR64R64Effect 0x11154d 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11154d 0 14).toInstrSpec (and_r64_r64_effect_step 0x11154d 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x111550 [0x4C, 0x31, 0xC0] (fun s => s.RIP = 0x111550) (xorR64R64Effect 0x111550 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111550 0 8).toInstrSpec (xor_r64_r64_effect_step 0x111550 0x4c 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11152d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111530) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111533) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111537) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11153a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 61), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11153d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111540) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111543) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 1), (2, 2), (3, 3), (4, 4), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111547) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 66), (1, 1), (2, 2), (3, 3), (4, 4), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 68), (22, 22), (39, 39), (51, 51)]) (p' := 0x11154a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (1, 1), (2, 2), (3, 3), (4, 4), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 68), (22, 22), (39, 39), (51, 51)]) (p' := 0x11154d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 1), (2, 2), (3, 3), (4, 4), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 68), (22, 22), (39, 39), (51, 51)]) (p' := 0x111550) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 1), (2, 2), (3, 3), (4, 4), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 68), (22, 22), (39, 39), (51, 51)]) (p' := 0x111553) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 76) (by decide) rfl

theorem block_l11700a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11700a :=
  Rest.liftedBlock (rest_l11700a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11700a x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
