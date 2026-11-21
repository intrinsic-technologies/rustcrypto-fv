import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Correction.l1181a0

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1181ad [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1126cd bytes_l1181ad) (entryMap (live .l1181ad))
      16 0x1126cd bytes_l1181ad b_l1181ad := by
  have f0 : InstrSpec 0x1126cd [0x4C, 0x8B, 0x16] (LoadPre 0x1126cd (fun s => AddrMode.addr (.base 6 .none) s (0x1126cd + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1126cd 10 (.base 6 .none))
      [.gpr 6] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1126cd 10 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1126cd 0x4c (by decide) 2 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1126d0 [0x4C, 0x8B, 0x4E, 0x08] (LoadPre 0x1126d0 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1126d0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1126d0 9 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1126d0 9 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1126d0 0x4c (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1126d4 [0x4C, 0x8B, 0x46, 0x10] (LoadPre 0x1126d4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1126d4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1126d4 8 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1126d4 8 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1126d4 0x4c (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1126d8 [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x1126d8 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1126d8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1126d8 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1126d8 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1126d8 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1126dc [0x48, 0x8B, 0x19] (LoadPre 0x1126dc (fun s => AddrMode.addr (.base 1 .none) s (0x1126dc + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1126dc 3 (.base 1 .none))
      [.gpr 1] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1126dc 3 (.base 1 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1126dc 0x48 (by decide) 3 (.base 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1126df [0x49, 0x89, 0xDB] (fun s => s.RIP = 0x1126df) (movR64R64Effect 0x1126df 11 3)
      [.gpr 3] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x1126df 11 3).toInstrSpec (mov_r64_r64_effect_step 0x1126df 0x49 0xdb (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1126e2 [0x4D, 0x29, 0xD3] (fun s => s.RIP = 0x1126e2) (subR64R64Effect 0x1126e2 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1126e2 11 10).toInstrSpec (sub_r64_r64_effect_step 0x1126e2 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1126e5 [0x48, 0xF7, 0xD3] (fun s => s.RIP = 0x1126e5) (notR64Effect 0x1126e5 3)
      [.gpr 3] [] [.reg 3, .rip] :=
    (notR64Effect_footprint 0x1126e5 3).toInstrSpec (not_r64_effect_step 0x1126e5 0x48 0xd3 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1126e8 [0x4D, 0x89, 0xD6] (fun s => s.RIP = 0x1126e8) (movR64R64Effect 0x1126e8 14 10)
      [.gpr 10] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1126e8 14 10).toInstrSpec (mov_r64_r64_effect_step 0x1126e8 0x4d 0xd6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1126eb [0x49, 0x21, 0xDE] (fun s => s.RIP = 0x1126eb) (andR64R64Effect 0x1126eb 14 3)
      [.gpr 14, .gpr 3] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1126eb 14 3).toInstrSpec (and_r64_r64_effect_step 0x1126eb 0x49 0xde (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1126ee [0x4C, 0x09, 0xD3] (fun s => s.RIP = 0x1126ee) (orR64R64Effect 0x1126ee 3 10)
      [.gpr 3, .gpr 10] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1126ee 3 10).toInstrSpec (or_r64_r64_effect_step 0x1126ee 0x4c 0xd3 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1126f1 [0x4C, 0x21, 0xDB] (fun s => s.RIP = 0x1126f1) (andR64R64Effect 0x1126f1 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1126f1 3 11).toInstrSpec (and_r64_r64_effect_step 0x1126f1 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1126f4 [0x4C, 0x09, 0xF3] (fun s => s.RIP = 0x1126f4) (orR64R64Effect 0x1126f4 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1126f4 3 14).toInstrSpec (or_r64_r64_effect_step 0x1126f4 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1126f7 [0x48, 0xC1, 0xEB, 0x3F] (fun s => s.RIP = 0x1126f7) (shrR64Effect 0x1126f7 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x1126f7 4 3 63).toInstrSpec (shr_r64_imm8_effect_step 0x1126f7 0x48 0xeb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1126fb [0x32, 0x56, 0x20] (LoadPre 0x1126fb (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1126fb + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1126fb 3 2 (.base 6 (.d8 0x20)))
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1126fb 3 2 (.base 6 (.d8 0x20))).toInstrSpec (xor_r8_m8_effect_step 0x1126fb 2 (by decide) (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1126fe [0x48, 0x89, 0x5C, 0x24, 0x08] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1126fe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1126fe + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1126fe 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1126fe 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1126fe 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (10, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x1126d0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (9, 55), (10, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x1126d4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 55), (10, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x1126d8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 55), (10, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x1126dc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 61), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 55), (10, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x1126df) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 61), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 55), (10, 53), (11, 63), (22, 22), (39, 39), (51, 51)]) (p' := 0x1126e2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 61), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 55), (10, 53), (11, 65), (22, 22), (39, 39), (51, 51)]) (p' := 0x1126e5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 67), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 55), (10, 53), (11, 65), (22, 22), (39, 39), (51, 51)]) (p' := 0x1126e8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 67), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 55), (10, 53), (11, 65), (14, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x1126eb) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 67), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 55), (10, 53), (11, 65), (14, 71), (22, 22), (39, 39), (51, 51)]) (p' := 0x1126ee) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 73), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 55), (10, 53), (11, 65), (14, 71), (22, 22), (39, 39), (51, 51)]) (p' := 0x1126f1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 75), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 55), (10, 53), (11, 65), (14, 71), (22, 22), (39, 39), (51, 51)]) (p' := 0x1126f4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 77), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 55), (10, 53), (11, 65), (14, 71), (22, 22), (39, 39), (51, 51)]) (p' := 0x1126f7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 79), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 55), (10, 53), (11, 65), (14, 71), (22, 22), (39, 39), (51, 51)]) (p' := 0x1126fb) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 59), (1, 1), (2, 81), (3, 79), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 55), (10, 53), (11, 65), (14, 71), (22, 22), (39, 39), (51, 51)]) (p' := 0x1126fe) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 59), (1, 1), (2, 81), (3, 79), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 55), (10, 53), (11, 65), (14, 71), (22, 22), (39, 39), (51, 51)]) (p' := 0x112703) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 84) (by decide) rfl

theorem block_l1181ad [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1181ad :=
  Rest.liftedBlock (rest_l1181ad code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1181ad x hx)

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine
