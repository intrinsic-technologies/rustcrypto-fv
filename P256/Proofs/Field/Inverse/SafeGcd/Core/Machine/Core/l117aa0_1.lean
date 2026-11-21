import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117aa0_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x111fc0 bytes_l117aa0) [(0, 0), (1, 1), (2, 86), (3, 78), (4, 4), (5, 88), (6, 6), (7, 7), (8, 71), (9, 67), (10, 82), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]
      5 0x11200f bytes_l117aa0_1 b_l117aa0_1 := by
  have f20 : InstrSpec 0x11200f [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x08] (LoadPre 0x11200f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11200f + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x11200f 6 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x11200f 6 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x11200f 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x112015 [0x49, 0xF7, 0xDF] (fun s => s.RIP = 0x112015) (negR64Effect 0x112015 15)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (negR64Effect_footprint 0x112015 15).toInstrSpec (neg_r64_effect_step 0x112015 0x49 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x112018 [0x48, 0x31, 0xEA] (fun s => s.RIP = 0x112018) (xorR64R64Effect 0x112018 2 5)
      [.gpr 2, .gpr 5] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x112018 2 5).toInstrSpec (xor_r64_r64_effect_step 0x112018 0x48 0xea (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x11201b [0x4C, 0x21, 0xFA] (fun s => s.RIP = 0x11201b) (andR64R64Effect 0x11201b 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11201b 2 15).toInstrSpec (and_r64_r64_effect_step 0x11201b 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x11201e [0x48, 0x31, 0xD5] (fun s => s.RIP = 0x11201e) (xorR64R64Effect 0x11201e 5 2)
      [.gpr 5, .gpr 2] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x11201e 5 2).toInstrSpec (xor_r64_r64_effect_step 0x11201e 0x48 0xd5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 1), (2, 86), (3, 78), (4, 4), (5, 88), (6, 6), (7, 7), (8, 71), (9, 67), (10, 82), (11, 53), (12, 12), (13, 13), (14, 14), (15, 91), (22, 22), (39, 39), (51, 51)]) (p' := 0x112015) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 0), (1, 1), (2, 86), (3, 78), (4, 4), (5, 88), (6, 6), (7, 7), (8, 71), (9, 67), (10, 82), (11, 53), (12, 12), (13, 13), (14, 14), (15, 93), (22, 22), (39, 39), (51, 51)]) (p' := 0x112018) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 0), (1, 1), (2, 95), (3, 78), (4, 4), (5, 88), (6, 6), (7, 7), (8, 71), (9, 67), (10, 82), (11, 53), (12, 12), (13, 13), (14, 14), (15, 93), (22, 22), (39, 39), (51, 51)]) (p' := 0x11201b) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 0), (1, 1), (2, 97), (3, 78), (4, 4), (5, 88), (6, 6), (7, 7), (8, 71), (9, 67), (10, 82), (11, 53), (12, 12), (13, 13), (14, 14), (15, 93), (22, 22), (39, 39), (51, 51)]) (p' := 0x11201e) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 0), (1, 1), (2, 97), (3, 78), (4, 4), (5, 99), (6, 6), (7, 7), (8, 71), (9, 67), (10, 82), (11, 53), (12, 12), (13, 13), (14, 14), (15, 93), (22, 22), (39, 39), (51, 51)]) (p' := 0x112021) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 101) (by decide) rfl

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
