import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117072 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111592 bytes_l117072) (entryMap (live .l117072))
      4 0x111592 bytes_l117072 b_l117072 := by
  have f0 : InstrSpec 0x111592 [0x48, 0x8B, 0x54, 0x24, 0x18] (LoadPre 0x111592 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111592 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111592 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x111592 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x111592 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x111597 [0x20, 0xCA] (fun s => s.RIP = 0x111597) (andR8R8Effect 0x111597 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (andR8R8Effect_footprint 0x111597 2 2 1).toInstrSpec (and_r8_r8_effect_step 0x111597 0xca (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x111599 [0x80, 0xF1, 0x01] (fun s => s.RIP = 0x111599) (xorR8Imm8Effect 0x111599 3 1 0x1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR8Imm8Effect_footprint 0x111599 3 1 0x1).toInstrSpec (xor_r8_imm8_effect_step 0x111599 0xf1 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11159c [0x22, 0x4C, 0x24, 0x20] (LoadPre 0x11159c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11159c + BitVec.ofNat 64 4)) 1) (andR8M8Effect 0x11159c 4 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (andR8M8Effect_footprint 0x11159c 4 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (and_r8_m8_effect_step 0x11159c 1 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)]) (p' := 0x111597) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)]) (p' := 0x111599) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 55), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)]) (p' := 0x11159c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 55), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115a0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l117072 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117072 :=
  Rest.liftedBlock (rest_l117072 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117072 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
