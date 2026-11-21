import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1171be [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1116de bytes_l1171be) (entryMap (live .l1171be))
      5 0x1116de bytes_l1171be b_l1171be := by
  have f0 : InstrSpec 0x1116de [0xB9, 0x40, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1116de) (movR32Imm32Effect 0x1116de 5 1 0x40)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1116de 5 1 0x40).toInstrSpec (mov_r32_imm32_effect_step 0x1116de 0xb9 (by decide) 0x40) pre_rip
  have f1 : InstrSpec 0x1116e3 [0x89, 0x6C, 0x24, 0x44] (StorePre 0x1116e3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x1116e3 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1116e3 5 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1116e3 5 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_m32_r32_low_effect_step 0x1116e3 5 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1116e7 [0x29, 0xE9] (fun s => s.RIP = 0x1116e7) (subR32R32Effect 0x1116e7 2 1 5)
      [.gpr 1, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (subR32R32Effect_footprint 0x1116e7 2 1 5).toInstrSpec (sub_r32_r32_effect_step 0x1116e7 0xe9 (by decide)) pre_rip
  have f3 : InstrSpec 0x1116e9 [0x83, 0xF9, 0x40] (fun s => s.RIP = 0x1116e9) (cmpR32Imm8Effect 0x1116e9 3 1 0x40)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1116e9 3 1 0x40).toInstrSpec (cmp_r32_imm8_effect_step 0x1116e9 0xf9 0x40 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (22, 22), (39, 39), (51, 51)]) (p' := 0x1116e3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (22, 22), (39, 39), (51, 51)]) (p' := 0x1116e7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 56), (3, 3), (4, 4), (5, 5), (22, 22), (39, 39), (51, 51)]) (p' := 0x1116e9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 56), (3, 3), (4, 4), (5, 5), (16, 58), (22, 22), (39, 39), (51, 51)]) (p' := 0x1116ec) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel32_effect_step 0x1116ec 3 0x447) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1171be [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1171be :=
  Rest.liftedBlock (rest_l1171be code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1171be x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
