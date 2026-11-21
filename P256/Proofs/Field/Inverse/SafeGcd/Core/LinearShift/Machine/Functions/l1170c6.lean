import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1170c6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1115e6 bytes_l1170c6) (entryMap (live .l1170c6))
      4 0x1115e6 bytes_l1170c6 b_l1170c6 := by
  have f0 : InstrSpec 0x1115e6 [0xB8, 0x40, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1115e6) (movR32Imm32Effect 0x1115e6 5 0 0x40)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1115e6 5 0 0x40).toInstrSpec (mov_r32_imm32_effect_step 0x1115e6 0xb8 (by decide) 0x40) pre_rip
  have f1 : InstrSpec 0x1115eb [0x29, 0xE8] (fun s => s.RIP = 0x1115eb) (subR32R32Effect 0x1115eb 2 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (subR32R32Effect_footprint 0x1115eb 2 0 5).toInstrSpec (sub_r32_r32_effect_step 0x1115eb 0xe8 (by decide)) pre_rip
  have f2 : InstrSpec 0x1115ed [0x83, 0xF8, 0x40] (fun s => s.RIP = 0x1115ed) (cmpR32Imm8Effect 0x1115ed 3 0 0x40)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1115ed 3 0 0x40).toInstrSpec (cmp_r32_imm8_effect_step 0x1115ed 0xf8 0x40 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115eb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115ed) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115f0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x1115f0 3 0x9c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1170c6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1170c6 :=
  Rest.liftedBlock (rest_l1170c6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1170c6 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine
