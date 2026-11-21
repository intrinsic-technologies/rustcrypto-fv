import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Core.l11795a_1
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l11795a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111e7a bytes_l11795a) (entryMap (live .l11795a))
      22 0x111e7a bytes_l11795a b_l11795a := by
  have f0 : InstrSpec 0x111e7a [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x111e7a) (addR64Imm8Effect 0x111e7a 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x111e7a 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x111e7a 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x111e7e [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x111e7e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x111e7e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111e7e 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x111e7e 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x111e7e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x111e83 [0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111e83 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x111e83 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111e83 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111e83 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111e83 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f3 : InstrSpec 0x111e8b [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x111e8b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x111e8b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111e8b 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x111e8b 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x111e8b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x111e90 [0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111e90 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x111e90 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111e90 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111e90 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111e90 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f5 : InstrSpec 0x111e98 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x111e98 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111e98 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111e98 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x111e98 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x111e98 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x111e9d [0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111e9d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x111e9d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111e9d 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111e9d 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111e9d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f7 : InstrSpec 0x111ea5 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x111ea5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111ea5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111ea5 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x111ea5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x111ea5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x111eaa [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x111eaa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111eaa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111eaa 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x111eaa 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x111eaa 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x111eaf [0x48, 0x89, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111eaf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x111eaf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111eaf 1 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111eaf 1 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111eaf 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f10 : InstrSpec 0x111eb7 [0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111eb7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x111eb7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111eb7 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111eb7 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111eb7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f11 : InstrSpec 0x111ebf [0x48, 0x8D, 0x54, 0x24, 0x30] (fun s => s.RIP = 0x111ebf) (leaR64Effect 0x111ebf 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x111ebf 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x111ebf 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x111ec4 [0x48, 0x8B, 0x02] (LoadPre 0x111ec4 (fun s => AddrMode.addr (.base 2 .none) s (0x111ec4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x111ec4 0 (.base 2 .none))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x111ec4 0 (.base 2 .none)).toInstrSpec (mov_r64_m64_effect_step 0x111ec4 0x48 (by decide) 0 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x111ec7 [0x48, 0x8B, 0x4A, 0x08] (LoadPre 0x111ec7 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x111ec7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111ec7 1 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x111ec7 1 (.base 2 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x111ec7 0x48 (by decide) 1 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x111ecb [0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111ecb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x111ecb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111ecb 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111ecb 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111ecb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f15 : InstrSpec 0x111ed3 [0x48, 0x89, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111ed3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x111ed3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111ed3 1 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111ed3 1 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111ed3 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f16 : InstrSpec 0x111edb [0x48, 0x8B, 0x42, 0x10] (LoadPre 0x111edb (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x111edb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111edb 0 (.base 2 (.d8 0x10)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x111edb 0 (.base 2 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x111edb 0x48 (by decide) 0 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x111edf [0x48, 0x89, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111edf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x111edf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111edf 0 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111edf 0 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111edf 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f18 : InstrSpec 0x111ee7 [0x48, 0x8B, 0x42, 0x18] (LoadPre 0x111ee7 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x111ee7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111ee7 0 (.base 2 (.d8 0x18)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x111ee7 0 (.base 2 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x111ee7 0x48 (by decide) 0 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x111eeb [0x48, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111eeb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x111eeb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111eeb 0 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111eeb 0 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111eeb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e7e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e83) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e8b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e90) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e98) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e9d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ea5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111eaa) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111eaf) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111eb7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ebf) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 64), (1, 66), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ec4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 66), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ec7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 72), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ecb) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 72), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ed3) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 72), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111edb) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111edf) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 78), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ee7) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111eeb) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 81), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ef3) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l11795a_1 code

theorem block_l11795a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11795a :=
  Rest.liftedBlock (rest_l11795a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11795a x hx)

section Steps

variable (code : CodeMap)
    (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64)
    (cf pf af zf sf of : Bool) (df : BitVec 1)
    (xmm0 xmm1 xmm2 xmm3 xmm4 xmm5 xmm6 xmm7 xmm8 xmm9 xmm10 xmm11 xmm12 xmm13 xmm14 xmm15 : BitVec 128)
    (mxcsr : BitVec 32) (st0 st1 st2 st3 st4 st5 st6 st7 : BitVec 80) (fsw : BitVec 16)
    (fcc : BitVec 4) (ftw fcw : BitVec 16) (fpuPtr : BitVec 171) (mem : Ram)

set_option hygiene false in
local notation "args" =>
  (#v[⟨64, rax⟩, ⟨64, rcx⟩, ⟨64, rdx⟩, ⟨64, rbx⟩, ⟨64, rsp⟩, ⟨64, rbp⟩, ⟨64, rsi⟩, ⟨64, rdi⟩, ⟨64, r8⟩, ⟨64, r9⟩, ⟨64, r10⟩, ⟨64, r11⟩, ⟨64, r12⟩, ⟨64, r13⟩, ⟨64, r14⟩, ⟨64, r15⟩] : Vector Value 16) ++
  (#v[.ofBool cf, .ofBool pf, .ofBool af, .ofBool zf, .ofBool sf, .ofBool of, ⟨1, df⟩] : Vector Value 7) ++
  (#v[⟨128, xmm0⟩, ⟨128, xmm1⟩, ⟨128, xmm2⟩, ⟨128, xmm3⟩, ⟨128, xmm4⟩, ⟨128, xmm5⟩, ⟨128, xmm6⟩, ⟨128, xmm7⟩, ⟨128, xmm8⟩, ⟨128, xmm9⟩, ⟨128, xmm10⟩, ⟨128, xmm11⟩, ⟨128, xmm12⟩, ⟨128, xmm13⟩, ⟨128, xmm14⟩, ⟨128, xmm15⟩, ⟨32, mxcsr⟩, ⟨80, st0⟩, ⟨80, st1⟩, ⟨80, st2⟩, ⟨80, st3⟩, ⟨80, st4⟩, ⟨80, st5⟩, ⟨80, st6⟩, ⟨80, st7⟩, ⟨16, fsw⟩, ⟨4, fcc⟩, ⟨16, ftw⟩, ⟨16, fcw⟩, ⟨171, fpuPtr⟩] : Vector Value 30)

theorem_by block_l11795a_eval :
    program.runBlock (dialect code) ⟨.l11795a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
