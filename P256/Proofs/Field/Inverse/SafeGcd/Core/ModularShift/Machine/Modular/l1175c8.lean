import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1175c8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111ae8 bytes_l1175c8) (entryMap (live .l1175c8))
      12 0x111ae8 bytes_l1175c8 b_l1175c8 := by
  have f0 : InstrSpec 0x111ae8 [0x88, 0x4C, 0x24, 0x10] (StorePre 0x111ae8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111ae8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111ae8 4 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111ae8 4 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x111ae8 1 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x111aec [0x0F, 0xB6, 0x54, 0x24, 0x10] (LoadPre 0x111aec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111aec + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111aec 5 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x111aec 5 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x111aec 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x111af1 [0x49, 0x31, 0xF4] (fun s => s.RIP = 0x111af1) (xorR64R64Effect 0x111af1 12 6)
      [.gpr 12, .gpr 6] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111af1 12 6).toInstrSpec (xor_r64_r64_effect_step 0x111af1 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x111af4 [0x48, 0xF7, 0xDA] (fun s => s.RIP = 0x111af4) (negR64Effect 0x111af4 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR64Effect_footprint 0x111af4 2).toInstrSpec (neg_r64_effect_step 0x111af4 0x48 0xda (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x111af7 [0x4C, 0x21, 0xE2] (fun s => s.RIP = 0x111af7) (andR64R64Effect 0x111af7 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111af7 2 12).toInstrSpec (and_r64_r64_effect_step 0x111af7 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x111afa [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x111afa) (xorR64R64Effect 0x111afa 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111afa 2 6).toInstrSpec (xor_r64_r64_effect_step 0x111afa 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x111afd [0x88, 0x4C, 0x24, 0x10] (StorePre 0x111afd 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111afd + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111afd 4 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111afd 4 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x111afd 1 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x111b01 [0x0F, 0xB6, 0x4C, 0x24, 0x10] (LoadPre 0x111b01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111b01 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111b01 5 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x111b01 5 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x111b01 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x111b06 [0x49, 0x31, 0xFB] (fun s => s.RIP = 0x111b06) (xorR64R64Effect 0x111b06 11 7)
      [.gpr 11, .gpr 7] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111b06 11 7).toInstrSpec (xor_r64_r64_effect_step 0x111b06 0x49 0xfb (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x111b09 [0x48, 0xF7, 0xD9] (fun s => s.RIP = 0x111b09) (negR64Effect 0x111b09 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR64Effect_footprint 0x111b09 1).toInstrSpec (neg_r64_effect_step 0x111b09 0x48 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x111b0c [0x4C, 0x21, 0xD9] (fun s => s.RIP = 0x111b0c) (andR64R64Effect 0x111b0c 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111b0c 1 11).toInstrSpec (and_r64_r64_effect_step 0x111b0c 0x4c 0xd9 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x111b0f [0x48, 0x31, 0xF9] (fun s => s.RIP = 0x111b0f) (xorR64R64Effect 0x111b0f 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111b0f 1 7).toInstrSpec (xor_r64_r64_effect_step 0x111b0f 0x48 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)]) (p' := 0x111aec) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 54), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)]) (p' := 0x111af1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 54), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x111af4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 58), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x111af7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x111afa) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 62), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x111afd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 62), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b01) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 62), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b06) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 65), (2, 62), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b09) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 69), (2, 62), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b0c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 71), (2, 62), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b0f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 73), (2, 62), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b12) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 75) (by decide) rfl

theorem block_l1175c8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1175c8 :=
  Rest.liftedBlock (rest_l1175c8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1175c8 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
