import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117671 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111b91 bytes_l117671) (entryMap (live .l117671))
      19 0x111b91 bytes_l117671 b_l117671 := by
  have f0 : InstrSpec 0x111b91 [0x49, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x111b91) (movR64Imm64Effect 0x111b91 9 0x7fffffffffffffff)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x111b91 9 0x7fffffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x111b91 0x49 0xb9 (by decide) (by decide) 0x7fffffffffffffff) pre_rip
  have f1 : InstrSpec 0x111b9b [0x48, 0x8B, 0x06] (LoadPre 0x111b9b (fun s => AddrMode.addr (.base 6 .none) s (0x111b9b + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x111b9b 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x111b9b 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x111b9b 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x111b9e [0x48, 0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111b9e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x111b9e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111b9e 0 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111b9e 0 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111b9e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f3 : InstrSpec 0x111ba6 [0x48, 0x8B, 0x46, 0x08] (LoadPre 0x111ba6 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x111ba6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111ba6 0 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x111ba6 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x111ba6 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x111baa [0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111baa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x111baa + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111baa 0 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111baa 0 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111baa 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f5 : InstrSpec 0x111bb2 [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x111bb2 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x111bb2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111bb2 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x111bb2 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x111bb2 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x111bb6 [0x48, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111bb6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x111bb6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111bb6 0 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111bb6 0 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111bb6 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f7 : InstrSpec 0x111bbe [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x111bbe (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x111bbe + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111bbe 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x111bbe 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x111bbe 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x111bc2 [0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111bc2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x111bc2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111bc2 0 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111bc2 0 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111bc2 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f9 : InstrSpec 0x111bca [0x48, 0x8B, 0x42, 0x18] (LoadPre 0x111bca (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x111bca + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111bca 0 (.base 2 (.d8 0x18)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x111bca 0 (.base 2 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x111bca 0x48 (by decide) 0 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x111bce [0x48, 0x89, 0x44, 0x24, 0x70] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111bce 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x111bce + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111bce 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111bce 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111bce 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f11 : InstrSpec 0x111bd3 [0x48, 0x8B, 0x42, 0x10] (LoadPre 0x111bd3 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x111bd3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111bd3 0 (.base 2 (.d8 0x10)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x111bd3 0 (.base 2 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x111bd3 0x48 (by decide) 0 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x111bd7 [0x48, 0x89, 0x44, 0x24, 0x68] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111bd7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x111bd7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111bd7 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111bd7 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111bd7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f13 : InstrSpec 0x111bdc [0x48, 0x8B, 0x02] (LoadPre 0x111bdc (fun s => AddrMode.addr (.base 2 .none) s (0x111bdc + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x111bdc 0 (.base 2 .none))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x111bdc 0 (.base 2 .none)).toInstrSpec (mov_r64_m64_effect_step 0x111bdc 0x48 (by decide) 0 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x111bdf [0x48, 0x89, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111bdf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x111bdf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111bdf 2 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111bdf 2 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111bdf 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f15 : InstrSpec 0x111be7 [0x48, 0x8B, 0x4A, 0x08] (LoadPre 0x111be7 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x111be7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111be7 1 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x111be7 1 (.base 2 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x111be7 0x48 (by decide) 1 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x111beb [0x48, 0x89, 0x4C, 0x24, 0x60] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111beb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x111beb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111beb 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111beb 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111beb 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f17 : InstrSpec 0x111bf0 [0x48, 0x89, 0x44, 0x24, 0x58] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111bf0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x111bf0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111bf0 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111bf0 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111bf0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f18 : InstrSpec 0x111bf5 [0xC6, 0x44, 0x24, 0x78, 0x00] (StorePre 0x111bf5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x111bf5 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x111bf5 (.sib 4 none 0 (.d8 0x78)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x111bf5 (.sib 4 none 0 (.d8 0x78)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x111bf5 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b9b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b9e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ba6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111baa) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111bb2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111bb6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111bbe) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111bc2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111bca) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111bce) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111bd3) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111bd7) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 70), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111bdc) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111bdf) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 73), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111be7) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 73), (1, 76), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111beb) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 73), (1, 76), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111bf0) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 73), (1, 76), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111bf5) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 73), (1, 76), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111bfa) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 81) (by decide) rfl

theorem block_l117671 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117671 :=
  Rest.liftedBlock (rest_l117671 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117671 x hx)

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

theorem_by block_l117671_eval :
    program.runBlock (dialect code) ⟨.l117671, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
