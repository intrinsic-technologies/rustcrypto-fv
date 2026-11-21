import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1179fa_1 [Bindings] (code : CodeMap) :
    Rest (n := 90) code lifted (codeRange 0x111f1a bytes_l1179fa) [(0, 87), (1, 78), (2, 83), (3, 3), (4, 4), (5, 5), (6, 85), (8, 75), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 76), (22, 22), (39, 39), (51, 51)]
      2 0x111f6e bytes_l1179fa_1 b_l1179fa_1 := by
  have f20 : InstrSpec 0x111f6e [0x44, 0x89, 0x44, 0x24, 0x04] (StorePre 0x111f6e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x111f6e + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x111f6e 8 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x111f6e 8 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_effect_step 0x111f6e 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 87), (1, 78), (2, 83), (3, 3), (4, 4), (5, 5), (6, 85), (8, 75), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f73) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jcc (n := 91) (jcc_rel32_effect_step 0x111f73 4 0xfffffd47) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
