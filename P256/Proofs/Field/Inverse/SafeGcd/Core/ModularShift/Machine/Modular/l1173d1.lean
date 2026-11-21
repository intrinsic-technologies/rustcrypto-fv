import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1173d1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1118f1 bytes_l1173d1) (entryMap (live .l1173d1))
      3 0x1118f1 bytes_l1173d1 b_l1173d1 := by
  have f0 : InstrSpec 0x1118f1 [0x44, 0x88, 0x4C, 0x24, 0x0E] (StorePre 0x1118f1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x1118f1 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1118f1 5 9 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1118f1 5 9 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1118f1 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1118f6 [0x83, 0x7C, 0x24, 0x44, 0x00] (LoadPre 0x1118f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x1118f6 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x1118f6 5 32 (.sib 4 none 0 (.d8 0x44)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x1118f6 5 (.sib 4 none 0 (.d8 0x44)) 0x0).toInstrSpec (cmp_m32_imm8_effect_step 0x1118f6 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1118f6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (51, 51)]) (p' := 0x1118fb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x1118fb 4 0x250) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1173d1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1173d1 :=
  Rest.liftedBlock (rest_l1173d1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1173d1 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
