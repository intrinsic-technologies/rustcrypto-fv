import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l114201_1 [Bindings] (code : CodeMap) :
    Rest (n := 82) code lifted (codeRange 0x1121b1 bytes_l114201) [(0, 79), (1, 74), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]
      7 0x112216 bytes_l114201_1 b_l114201_1 := by
  have f20 : InstrSpec 0x112216 [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x112216 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x112216 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112216 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x112216 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x112216 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x11221a [0x48, 0x89, 0x44, 0x24, 0x40] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11221a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11221a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11221a 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11221a 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x11221a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f22 : InstrSpec 0x11221f [0x48, 0x8B, 0x06] (LoadPre 0x11221f (fun s => AddrMode.addr (.base 6 .none) s (0x11221f + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11221f 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11221f 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11221f 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x112222 [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x112222 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x112222 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112222 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x112222 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x112222 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x112226 [0x48, 0x89, 0x4C, 0x24, 0x38] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112226 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x112226 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112226 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112226 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112226 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f25 : InstrSpec 0x11222b [0x48, 0x89, 0x44, 0x24, 0x30] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11222b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11222b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11222b 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11222b 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x11222b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f26 : InstrSpec 0x112230 [0xC6, 0x44, 0x24, 0x50, 0x00] (StorePre 0x112230 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x112230 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x112230 (.sib 4 none 0 (.d8 0x50)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x112230 (.sib 4 none 0 (.d8 0x50)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x112230 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 82), (1, 74), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11221a) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 82), (1, 74), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11221f) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (1, 74), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112222) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 85), (1, 87), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112226) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 85), (1, 87), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11222b) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 85), (1, 87), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112230) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 85), (1, 87), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112235) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 92) (by decide) rfl

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
