import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1171d2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1116f2 bytes_l1171d2) (entryMap (live .l1171d2))
      9 0x1116f2 bytes_l1171d2 b_l1171d2 := by
  have f0 : InstrSpec 0x1116f2 [0x48, 0x89, 0x5C, 0x24, 0x70] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1116f2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1116f2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1116f2 3 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1116f2 3 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1116f2 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1116f7 [0x48, 0x8B, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x1116f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1116f7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1116f7 7 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1116f7 7 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x1116f7 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1116ff [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x1116ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1116ff + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1116ff 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1116ff 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1116ff 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x111704 [0x4C, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x111704 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x111704 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111704 9 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x111704 9 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x111704 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x11170c [0x4C, 0x0F, 0xAF, 0xCE] (fun s => s.RIP = 0x11170c) (imulR64R64Effect 0x11170c 4 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x11170c 4 9 6).toInstrSpec (imul_r64_r64_effect_step 0x11170c 0x4c (by decide) 0xce (by decide)) pre_rip
  have f5 : InstrSpec 0x111710 [0x49, 0xD3, 0xE1] (fun s => s.RIP = 0x111710) (shlR64ClEffect 0x111710 3 9)
      [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x111710 3 9).toInstrSpec (shl_r64_cl_effect_step 0x111710 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x111713 [0x49, 0xD3, 0xE9] (fun s => s.RIP = 0x111713) (shrR64ClEffect 0x111713 3 9)
      [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x111713 3 9).toInstrSpec (shr_r64_cl_effect_step 0x111713 0x49 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111716 [0x4C, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x111716 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111716 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111716 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x111716 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x111716 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x11171b [0x48, 0x8B, 0x5C, 0x24, 0x20] (LoadPre 0x11171b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11171b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11171b 3 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x11171b 3 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x11171b 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (22, 22), (39, 39), (51, 51)]) (p' := 0x1116f7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(1, 1), (3, 3), (4, 4), (7, 54), (22, 22), (39, 39), (51, 51)]) (p' := 0x1116ff) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 56), (7, 54), (22, 22), (39, 39), (51, 51)]) (p' := 0x111704) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 56), (7, 54), (9, 58), (22, 22), (39, 39), (51, 51)]) (p' := 0x11170c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 56), (7, 54), (9, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x111710) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 56), (7, 54), (9, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x111713) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 56), (7, 54), (9, 64), (22, 22), (39, 39), (51, 51)]) (p' := 0x111716) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (22, 22), (39, 39), (51, 51)]) (p' := 0x11171b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 1), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (22, 22), (39, 39), (51, 51)]) (p' := 0x111720) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 70) (by decide) rfl

theorem block_l1171d2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1171d2 :=
  Rest.liftedBlock (rest_l1171d2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1171d2 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
