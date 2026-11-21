import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l116fbb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1114db bytes_l116fbb) (entryMap (live .l116fbb))
      7 0x1114db bytes_l116fbb b_l116fbb := by
  have f0 : InstrSpec 0x1114db [0x48, 0x89, 0xE1] (fun s => s.RIP = 0x1114db) (movR64R64Effect 0x1114db 1 4)
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1114db 1 4).toInstrSpec (mov_r64_r64_effect_step 0x1114db 0x48 0xe1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1114de [0x0F, 0xB6, 0x4C, 0x24, 0x10] (LoadPre 0x1114de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1114de + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1114de 5 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1114de 5 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x1114de 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1114e3 [0x80, 0xE1, 0x01] (fun s => s.RIP = 0x1114e3) (andR8Imm8Effect 0x1114e3 3 1 0x1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x1114e3 3 1 0x1).toInstrSpec (and_r8_imm8_effect_step 0x1114e3 0xe1 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1114e6 [0x48, 0x83, 0x3C, 0x24, 0x00] (LoadPre 0x1114e6 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1114e6 + BitVec.ofNat 64 5)) 8) (cmpMImm8Effect 0x1114e6 5 64 (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect64_footprint 0x1114e6 5 (.sib 4 none 0 .none) 0x0).toInstrSpec (cmp_m64_imm8_effect_step 0x1114e6 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1114eb [0x0F, 0xB6, 0xC9] (fun s => s.RIP = 0x1114eb) (movzxR32R8Effect 0x1114eb 3 1 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x1114eb 3 1 1).toInstrSpec (movzx_r32_r8_effect_step 0x1114eb 0xc9 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1114ee [0x41, 0xBD, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1114ee) (movR32Imm32Effect 0x1114ee 6 13 0x0)
      [] [] [.reg 13, .rip] :=
    (movR32Imm32Effect_footprint 0x1114ee 6 13 0x0).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1114ee 0x41 0xbd (by decide) (by decide) 0x0) pre_rip
  have f6 : InstrSpec 0x1114f4 [0x41, 0x0F, 0x44, 0xCD] (fun s => s.RIP = 0x1114f4) (atFlags (condHolds 4) (cmovR32R32Effect 0x1114f4 4 1 13))
      [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (cmovR32R32Effect_footprint 0x1114f4 4 1 13 4).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_rex_effect_step 0x1114f4 4 0x41 (by decide) 0xcd (by decide) c)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114de) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 54), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114e3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114e6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (19, 58), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114eb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 60), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (19, 58), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114ee) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 60), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (13, 62), (19, 58), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114f4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 64), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (13, 62), (19, 58), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114f8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 66) (by decide) rfl

theorem block_l116fbb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l116fbb :=
  Rest.liftedBlock (rest_l116fbb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l116fbb x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
