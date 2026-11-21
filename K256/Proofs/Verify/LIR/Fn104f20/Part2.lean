import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

theorem rest_l1060c7_1 [Bindings] (code : CodeMap) :
    Rest (n := 97) code lifted (codeRange 0x1060c7 bytes_l1060c7) [(0, 69), (1, 75), (2, 2), (3, 79), (4, 95), (5, 94), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 82), (13, 85), (14, 88), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x106117 bytes_l1060c7_1 b_l1060c7_1 := by
  have f20 : InstrSpec 0x106117 [0xC3] (RetPre 0x106117) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x106117).toInstrSpec (ret_effect_step 0x106117) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f20 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 98) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 99) (ρ' := [(0, 69), (1, 75), (2, 2), (3, 79), (4, 98), (5, 94), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 82), (13, 85), (14, 88), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) f20 (by decide) rfl rfl rfl (by decide)

theorem rest_l1060c7 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1060c7 bytes_l1060c7) (entryMap (live .l1060c7))
      21 0x1060c7 bytes_l1060c7 b_l1060c7 := by
  have f0 : InstrSpec 0x1060c7 [0x48, 0x8B, 0x04, 0x24] (LoadPre 0x1060c7 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1060c7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1060c7 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1060c7 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1060c7 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1060cb [0x48, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x1060cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1060cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1060cb 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1060cb 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1060cb 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1060d0 [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x1060d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1060d0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1060d0 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1060d0 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x1060d0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1060d5 [0x48, 0x89, 0x4C, 0x24, 0x70] (StorePre 0x1060d5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1060d5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1060d5 1 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1060d5 1 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x1060d5 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1060da [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1060da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1060da + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1060da 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1060da 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1060da 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1060df [0x48, 0x89, 0x44, 0x24, 0x78] (StorePre 0x1060df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1060df + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1060df 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1060df 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x1060df 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1060e4 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x1060e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1060e4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1060e4 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1060e4 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1060e4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1060e9 [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x1060e9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1060e9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1060e9 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1060e9 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x1060e9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1060f1 [0x48, 0x8D, 0x74, 0x24, 0x68] (fun s => s.RIP = 0x1060f1) (leaR64Effect 0x1060f1 6 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1060f1 6 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (lea_r64_effect_step 0x1060f1 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1060f6 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1060f6) (movR32Imm32Effect 0x1060f6 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1060f6 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1060f6 0xb9 (by decide) 0xf) pre_rip
  have f10 : InstrSpec 0x1060fb [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x1060fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1060fb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1060fb 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1060fb 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1060fb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x106100 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x106100) (movR64R64Effect 0x106100 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x106100 7 0).toInstrSpec (mov_r64_r64_effect_step 0x106100 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x106103 [0xF3, 0x48, 0xA5] (RepPre 0x106103 (RepMovsqPre 0x106103)) (repMovsqEffect 0x106103)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x106103).toInstrSpecOfRuns (rep_movsq_runs hstride 0x106103 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f13 : InstrSpec 0x106106 [0x48, 0x81, 0xC4, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x106106) (addR64Imm32Effect 0x106106 4 0x158)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x106106 4 0x158).toInstrSpec (add_r64_imm32_effect_step 0x106106 0x48 0xc4 0x158 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10610d [0x5B] (PopPre 0x10610d) (popR64Effect 0x10610d 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10610d 1 3).toInstrSpec (pop_r64_effect_step 0x10610d 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f15 : InstrSpec 0x10610e [0x41, 0x5C] (PopPre 0x10610e) (popR64Effect 0x10610e 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10610e 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10610e 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f16 : InstrSpec 0x106110 [0x41, 0x5D] (PopPre 0x106110) (popR64Effect 0x106110 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106110 2 13).toInstrSpec (pop_r64_rex_effect_step 0x106110 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f17 : InstrSpec 0x106112 [0x41, 0x5E] (PopPre 0x106112) (popR64Effect 0x106112 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106112 2 14).toInstrSpec (pop_r64_rex_effect_step 0x106112 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f18 : InstrSpec 0x106114 [0x41, 0x5F] (PopPre 0x106114) (popR64Effect 0x106114 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106114 2 15).toInstrSpec (pop_r64_rex_effect_step 0x106114 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f19 : InstrSpec 0x106116 [0x5D] (PopPre 0x106116) (popR64Effect 0x106116 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106116 1 5).toInstrSpec (pop_r64_effect_step 0x106116 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060cb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060d0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060d5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060da) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060df) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 55), (2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060e4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 55), (2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060e9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 55), (2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060f1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 55), (2, 2), (4, 4), (6, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060f6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 62), (1, 67), (2, 2), (4, 4), (6, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060fb) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 67), (2, 2), (4, 4), (6, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106100) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 67), (2, 2), (4, 4), (6, 65), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106103) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 75) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 76) (ρ' := [(0, 69), (1, 75), (2, 2), (4, 4), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106106) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 69), (1, 75), (2, 2), (4, 77), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10610d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 80) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 81) (ρ' := [(0, 69), (1, 75), (2, 2), (3, 79), (4, 80), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10610e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 69), (1, 75), (2, 2), (3, 79), (4, 83), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106110) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 69), (1, 75), (2, 2), (3, 79), (4, 86), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 82), (13, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106112) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f17 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 89) f17 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 90) (ρ' := [(0, 69), (1, 75), (2, 2), (3, 79), (4, 89), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 82), (13, 85), (14, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106114) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f18 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 92) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 93) (ρ' := [(0, 69), (1, 75), (2, 2), (3, 79), (4, 92), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 82), (13, 85), (14, 88), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106116) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f19 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 95) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 96) (ρ' := [(0, 69), (1, 75), (2, 2), (3, 79), (4, 95), (5, 94), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 82), (13, 85), (14, 88), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106117) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1060c7_1 code

theorem block_l1060c7 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1060c7 :=
  Rest.liftedBlock (rest_l1060c7 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1060c7 x hx)

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

theorem_by block_l1060c7_eval :
    program.runBlock (dialect code) ⟨.l1060c7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
