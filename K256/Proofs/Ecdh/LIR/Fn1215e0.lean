import K256.Proofs.Ecdh.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Ecdh.LIR.Generated.Values

namespace K256.Proofs.Ecdh.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR

theorem rest_l1215e0_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x1215e0 bytes_l1215e0) [(0, 78), (1, 80), (2, 2), (3, 67), (4, 61), (5, 63), (6, 86), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x12162b bytes_l1215e0_1 b_l1215e0_1 := by
  have f20 : InstrSpec 0x12162b [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x12162b) (movR64R64Effect 0x12162b 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12162b 7 15).toInstrSpec (mov_r64_r64_effect_step 0x12162b 0x4c 0xff (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x12162e [0xE8, 0xFD, 0x32, 0xFF, 0xFF] (PushPre 0x12162e 5) (callEffect (fun _ => 0x114930) 0x121633)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12162e 0x114930 0x121633).toInstrSpec (call_rel32_effect_step 0x12162e 0xffff32fd (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f20 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 78), (1, 80), (2, 2), (3, 67), (4, 61), (5, 63), (6, 86), (7, 88), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12162e) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f21 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 78), (1, 80), (2, 2), (3, 67), (4, 90), (5, 63), (6, 86), (7, 88), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114930) f21 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 92) (by decide) (by decide) rfl rfl

theorem rest_l1215e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1215e0 bytes_l1215e0) (entryMap (live .l1215e0))
      22 0x1215e0 bytes_l1215e0 b_l1215e0 := by
  have f0 : InstrSpec 0x1215e0 [0x55] (PushPre 0x1215e0 1) (pushR64Effect 0x1215e0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1215e0 1 5).toInstrSpec (push_r64_effect_step 0x1215e0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1215e1 [0x41, 0x57] (PushPre 0x1215e1 2) (pushR64Effect 0x1215e1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1215e1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1215e1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1215e3 [0x41, 0x56] (PushPre 0x1215e3 2) (pushR64Effect 0x1215e3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1215e3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1215e3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1215e5 [0x53] (PushPre 0x1215e5 1) (pushR64Effect 0x1215e5 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1215e5 1 3).toInstrSpec (push_r64_effect_step 0x1215e5 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1215e6 [0x48, 0x81, 0xEC, 0x18, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1215e6) (subR64Imm32Effect 0x1215e6 4 0x118)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x1215e6 4 0x118).toInstrSpec (sub_r64_imm32_effect_step 0x1215e6 0x48 0xec 0x118 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1215ed [0x89, 0xD5] (fun s => s.RIP = 0x1215ed) (movR32R32Effect 0x1215ed 2 5 2)
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x1215ed 2 5 2).toInstrSpec (mov_r32_r32_effect_step 0x1215ed 0xd5 (by decide)) pre_rip
  have f6 : InstrSpec 0x1215ef [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x1215ef) (movR64R64Effect 0x1215ef 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1215ef 14 6).toInstrSpec (mov_r64_r64_effect_step 0x1215ef 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1215f2 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x1215f2) (movR64R64Effect 0x1215f2 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1215f2 3 7).toInstrSpec (mov_r64_r64_effect_step 0x1215f2 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1215f5 [0x48, 0x8B, 0x46, 0x20] (LoadPre 0x1215f5 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1215f5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1215f5 0 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1215f5 0 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1215f5 0x48 (by decide) 0 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1215f9 [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x1215f9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1215f9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1215f9 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1215f9 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1215f9 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1215fe [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x1215fe (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1215fe + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1215fe 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1215fe 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1215fe 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x121602 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x121602 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x121602 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121602 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121602 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x121602 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x121607 [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x121607 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x121607 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x121607 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x121607 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x121607 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x12160b [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x12160b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12160b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12160b 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12160b 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x12160b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x121610 [0x48, 0x8B, 0x06] (LoadPre 0x121610 (fun s => AddrMode.addr (.base 6 .none) s (0x121610 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x121610 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x121610 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x121610 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x121613 [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x121613 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x121613 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x121613 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x121613 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x121613 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x121617 [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x121617 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x121617 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121617 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121617 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x121617 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x12161c [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x12161c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12161c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12161c 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12161c 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x12161c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x121621 [0x4C, 0x8D, 0x7C, 0x24, 0x50] (fun s => s.RIP = 0x121621) (leaR64Effect 0x121621 15 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x121621 15 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x121621 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x121626 [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x121626) (leaR64Effect 0x121626 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x121626 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x121626 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215e1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215e3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215e5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215e6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215ed) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 63), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215ef) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 63), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215f2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 67), (4, 61), (5, 63), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215f5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (2, 2), (3, 67), (4, 61), (5, 63), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215f9) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (2, 2), (3, 67), (4, 61), (5, 63), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215fe) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (2, 2), (3, 67), (4, 61), (5, 63), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121602) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (2, 2), (3, 67), (4, 61), (5, 63), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121607) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (2, 2), (3, 67), (4, 61), (5, 63), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12160b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (2, 2), (3, 67), (4, 61), (5, 63), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121610) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (2, 2), (3, 67), (4, 61), (5, 63), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121613) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 78), (1, 80), (2, 2), (3, 67), (4, 61), (5, 63), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121617) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 78), (1, 80), (2, 2), (3, 67), (4, 61), (5, 63), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12161c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 78), (1, 80), (2, 2), (3, 67), (4, 61), (5, 63), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121621) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f18 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 78), (1, 80), (2, 2), (3, 67), (4, 61), (5, 63), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121626) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f19 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 78), (1, 80), (2, 2), (3, 67), (4, 61), (5, 63), (6, 86), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12162b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1215e0_1 code

theorem block_l1215e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1215e0 :=
  Rest.liftedBlock (rest_l1215e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1215e0 x hx)

theorem rest_l121633 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121633 bytes_l121633) (entryMap (live .l121633))
      3 0x121633 bytes_l121633 b_l121633 := by
  have f0 : InstrSpec 0x121633 [0x48, 0x8D, 0xBC, 0x24, 0x97, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x121633) (leaR64Effect 0x121633 7 (.sib 4 none 0 (.d32 0x97)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x121633 7 (.sib 4 none 0 (.d32 0x97))).toInstrSpec (lea_r64_effect_step 0x121633 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x97)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12163b [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x12163b) (movR64R64Effect 0x12163b 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12163b 6 15).toInstrSpec (mov_r64_r64_effect_step 0x12163b 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12163e [0xE8, 0x8D, 0x32, 0xFF, 0xFF] (PushPre 0x12163e 5) (callEffect (fun _ => 0x1148d0) 0x121643)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12163e 0x1148d0 0x121643).toInstrSpec (call_rel32_effect_step 0x12163e 0xffff328d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12163b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12163e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148d0) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l121633 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121633 :=
  Rest.liftedBlock (rest_l121633 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121633 x hx)

theorem rest_l121643 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121643 bytes_l121643) (entryMap (live .l121643))
      14 0x121643 bytes_l121643 b_l121643 := by
  have f0 : InstrSpec 0x121643 [0x49, 0x8B, 0x46, 0x48] (LoadPre 0x121643 (fun s => AddrMode.addr (.base 14 (.d8 0x48)) s (0x121643 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x121643 0 (.base 14 (.d8 0x48)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x121643 0 (.base 14 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x121643 0x49 (by decide) 0 (.base 14 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x121647 [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x121647 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x121647 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121647 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121647 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x121647 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12164c [0x49, 0x8B, 0x46, 0x40] (LoadPre 0x12164c (fun s => AddrMode.addr (.base 14 (.d8 0x40)) s (0x12164c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12164c 0 (.base 14 (.d8 0x40)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12164c 0 (.base 14 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x12164c 0x49 (by decide) 0 (.base 14 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x121650 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x121650 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x121650 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121650 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121650 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x121650 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x121655 [0x49, 0x8B, 0x46, 0x38] (LoadPre 0x121655 (fun s => AddrMode.addr (.base 14 (.d8 0x38)) s (0x121655 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x121655 0 (.base 14 (.d8 0x38)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x121655 0 (.base 14 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x121655 0x49 (by decide) 0 (.base 14 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x121659 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x121659 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121659 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121659 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121659 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x121659 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x12165e [0x49, 0x8B, 0x46, 0x28] (LoadPre 0x12165e (fun s => AddrMode.addr (.base 14 (.d8 0x28)) s (0x12165e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12165e 0 (.base 14 (.d8 0x28)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12165e 0 (.base 14 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x12165e 0x49 (by decide) 0 (.base 14 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x121662 [0x49, 0x8B, 0x4E, 0x30] (LoadPre 0x121662 (fun s => AddrMode.addr (.base 14 (.d8 0x30)) s (0x121662 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x121662 1 (.base 14 (.d8 0x30)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x121662 1 (.base 14 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x121662 0x49 (by decide) 1 (.base 14 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x121666 [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x121666 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x121666 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121666 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121666 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x121666 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12166b [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x12166b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12166b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12166b 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12166b 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x12166b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x121670 [0x4C, 0x8D, 0x7C, 0x24, 0x50] (fun s => s.RIP = 0x121670) (leaR64Effect 0x121670 15 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x121670 15 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x121670 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x121675 [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x121675) (leaR64Effect 0x121675 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x121675 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x121675 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x12167a [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x12167a) (movR64R64Effect 0x12167a 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12167a 7 15).toInstrSpec (mov_r64_r64_effect_step 0x12167a 0x4c 0xff (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x12167d [0xE8, 0xAE, 0x32, 0xFF, 0xFF] (PushPre 0x12167d 5) (callEffect (fun _ => 0x114930) 0x121682)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12167d 0x114930 0x121682).toInstrSpec (call_rel32_effect_step 0x12167d 0xffff32ae (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121647) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12164c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121650) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121655) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121659) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12165e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121662) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121666) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12166b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121670) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121675) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (6, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12167a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (6, 70), (7, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12167d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 74), (5, 5), (6, 70), (7, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114930) f13 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 76) (by decide) (by decide) rfl rfl

theorem block_l121643 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121643 :=
  Rest.liftedBlock (rest_l121643 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121643 x hx)

theorem rest_l121682 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121682 bytes_l121682) (entryMap (live .l121682))
      3 0x121682 bytes_l121682 b_l121682 := by
  have f0 : InstrSpec 0x121682 [0x48, 0x8D, 0xBC, 0x24, 0xB7, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x121682) (leaR64Effect 0x121682 7 (.sib 4 none 0 (.d32 0xb7)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x121682 7 (.sib 4 none 0 (.d32 0xb7))).toInstrSpec (lea_r64_effect_step 0x121682 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb7)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12168a [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x12168a) (movR64R64Effect 0x12168a 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12168a 6 15).toInstrSpec (mov_r64_r64_effect_step 0x12168a 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12168d [0xE8, 0x3E, 0x32, 0xFF, 0xFF] (PushPre 0x12168d 5) (callEffect (fun _ => 0x1148d0) 0x121692)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12168d 0x1148d0 0x121692).toInstrSpec (call_rel32_effect_step 0x12168d 0xffff323e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12168a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12168d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148d0) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l121682 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121682 :=
  Rest.liftedBlock (rest_l121682 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121682 x hx)

theorem rest_l121692 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121692 bytes_l121692) (entryMap (live .l121692))
      2 0x121692 bytes_l121692 b_l121692 := by
  have f0 : InstrSpec 0x121692 [0x85, 0xED] (fun s => s.RIP = 0x121692) (testR32R32Effect 0x121692 2 5 5)
      [.gpr 5, .gpr 5] [] [.flags, .rip] :=
    (testR32R32Effect_footprint 0x121692 2 5 5).toInstrSpec (test_r32_r32_effect_step 0x121692 0xed (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121694) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x121694 4 0x6c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l121692 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121692 :=
  Rest.liftedBlock (rest_l121692 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121692 x hx)

theorem rest_l121696 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121696 bytes_l121696) (entryMap (live .l121696))
      3 0x121696 bytes_l121696 b_l121696 := by
  have f0 : InstrSpec 0x121696 [0x48, 0x8D, 0xBC, 0x24, 0xB7, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x121696) (leaR64Effect 0x121696 7 (.sib 4 none 0 (.d32 0xb7)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x121696 7 (.sib 4 none 0 (.d32 0xb7))).toInstrSpec (lea_r64_effect_step 0x121696 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb7)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12169e [0xBE, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12169e) (movR32Imm32Effect 0x12169e 5 6 0x20)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x12169e 5 6 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x12169e 0xbe (by decide) 0x20) pre_rip
  have f2 : InstrSpec 0x1216a3 [0xE8, 0xB8, 0x40, 0x00, 0x00] (PushPre 0x1216a3 5) (callEffect (fun _ => 0x125760) 0x1216a8)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1216a3 0x125760 0x1216a8).toInstrSpec (call_rel32_effect_step 0x1216a3 0x40b8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12169e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1216a3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125760) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l121696 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121696 :=
  Rest.liftedBlock (rest_l121696 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121696 x hx)

theorem rest_l1216a8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1216a8 bytes_l1216a8) (entryMap (live .l1216a8))
      13 0x1216a8 bytes_l1216a8 b_l1216a8 := by
  have f0 : InstrSpec 0x1216a8 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1216a8 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1216a8 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1216a8 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1216a8 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1216a8 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1216b1 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1216b1 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1216b1 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1216b1 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1216b1 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1216b1 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1216ba [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1216ba 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1216ba + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1216ba (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1216ba (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1216ba 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1216c3 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1216c3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1216c3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1216c3 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1216c3 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1216c3 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1216cc [0x48, 0x8B, 0x8C, 0x24, 0x97, 0x00, 0x00, 0x00] (LoadPre 0x1216cc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x97)) s (0x1216cc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1216cc 1 (.sib 4 none 0 (.d32 0x97)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1216cc 1 (.sib 4 none 0 (.d32 0x97))).toInstrSpec (mov_r64_m64_effect_step 0x1216cc 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x97)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1216d4 [0x48, 0x8B, 0x94, 0x24, 0x9F, 0x00, 0x00, 0x00] (LoadPre 0x1216d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x1216d4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1216d4 2 (.sib 4 none 0 (.d32 0x9f)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1216d4 2 (.sib 4 none 0 (.d32 0x9f))).toInstrSpec (mov_r64_m64_effect_step 0x1216d4 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x9f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1216dc [0x48, 0x89, 0x4C, 0x24, 0x50] (StorePre 0x1216dc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1216dc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1216dc 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1216dc 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x1216dc 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1216e1 [0x48, 0x89, 0x54, 0x24, 0x58] (StorePre 0x1216e1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1216e1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1216e1 2 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1216e1 2 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x1216e1 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1216e6 [0x48, 0x8B, 0x8C, 0x24, 0xA7, 0x00, 0x00, 0x00] (LoadPre 0x1216e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa7)) s (0x1216e6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1216e6 1 (.sib 4 none 0 (.d32 0xa7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1216e6 1 (.sib 4 none 0 (.d32 0xa7))).toInstrSpec (mov_r64_m64_effect_step 0x1216e6 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1216ee [0x48, 0x89, 0x4C, 0x24, 0x60] (StorePre 0x1216ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1216ee + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1216ee 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1216ee 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x1216ee 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1216f3 [0x48, 0x8B, 0x8C, 0x24, 0xAF, 0x00, 0x00, 0x00] (LoadPre 0x1216f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaf)) s (0x1216f3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1216f3 1 (.sib 4 none 0 (.d32 0xaf)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1216f3 1 (.sib 4 none 0 (.d32 0xaf))).toInstrSpec (mov_r64_m64_effect_step 0x1216f3 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xaf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1216fb [0x48, 0x89, 0x4C, 0x24, 0x68] (StorePre 0x1216fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1216fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1216fb 1 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1216fb 1 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x1216fb 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1216b1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1216ba) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1216c3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1216cc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1216d4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1216dc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1216e1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1216e6) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1216ee) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 63), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1216f3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 66), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1216fb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 66), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121700) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 69) (jmp_rel8_effect_step 0x121700 0x6a (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1216a8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1216a8 :=
  Rest.liftedBlock (rest_l1216a8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1216a8 x hx)

theorem rest_l121702 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121702 bytes_l121702) (entryMap (live .l121702))
      17 0x121702 bytes_l121702 b_l121702 := by
  have f0 : InstrSpec 0x121702 [0x48, 0x8B, 0x84, 0x24, 0x97, 0x00, 0x00, 0x00] (LoadPre 0x121702 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x97)) s (0x121702 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x121702 0 (.sib 4 none 0 (.d32 0x97)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x121702 0 (.sib 4 none 0 (.d32 0x97))).toInstrSpec (mov_r64_m64_effect_step 0x121702 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x97)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12170a [0x48, 0x8B, 0x8C, 0x24, 0x9F, 0x00, 0x00, 0x00] (LoadPre 0x12170a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x12170a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12170a 1 (.sib 4 none 0 (.d32 0x9f)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12170a 1 (.sib 4 none 0 (.d32 0x9f))).toInstrSpec (mov_r64_m64_effect_step 0x12170a 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x9f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x121712 [0x48, 0x89, 0x44, 0x24, 0x50] (StorePre 0x121712 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x121712 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121712 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121712 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x121712 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x121717 [0x48, 0x89, 0x4C, 0x24, 0x58] (StorePre 0x121717 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x121717 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121717 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121717 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x121717 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12171c [0x48, 0x8B, 0x84, 0x24, 0xA7, 0x00, 0x00, 0x00] (LoadPre 0x12171c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa7)) s (0x12171c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12171c 0 (.sib 4 none 0 (.d32 0xa7)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12171c 0 (.sib 4 none 0 (.d32 0xa7))).toInstrSpec (mov_r64_m64_effect_step 0x12171c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x121724 [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x121724 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x121724 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121724 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121724 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x121724 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x121729 [0x48, 0x8B, 0x84, 0x24, 0xAF, 0x00, 0x00, 0x00] (LoadPre 0x121729 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaf)) s (0x121729 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x121729 0 (.sib 4 none 0 (.d32 0xaf)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x121729 0 (.sib 4 none 0 (.d32 0xaf))).toInstrSpec (mov_r64_m64_effect_step 0x121729 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xaf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x121731 [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x121731 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x121731 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121731 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121731 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x121731 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x121736 [0x48, 0x8B, 0x84, 0x24, 0xB7, 0x00, 0x00, 0x00] (LoadPre 0x121736 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb7)) s (0x121736 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x121736 0 (.sib 4 none 0 (.d32 0xb7)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x121736 0 (.sib 4 none 0 (.d32 0xb7))).toInstrSpec (mov_r64_m64_effect_step 0x121736 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x12173e [0x48, 0x8B, 0x8C, 0x24, 0xBF, 0x00, 0x00, 0x00] (LoadPre 0x12173e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbf)) s (0x12173e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12173e 1 (.sib 4 none 0 (.d32 0xbf)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12173e 1 (.sib 4 none 0 (.d32 0xbf))).toInstrSpec (mov_r64_m64_effect_step 0x12173e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xbf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x121746 [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x121746 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x121746 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121746 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121746 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x121746 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x12174b [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x12174b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12174b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12174b 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12174b 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x12174b 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x121750 [0x48, 0x8B, 0x84, 0x24, 0xC7, 0x00, 0x00, 0x00] (LoadPre 0x121750 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc7)) s (0x121750 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x121750 0 (.sib 4 none 0 (.d32 0xc7)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x121750 0 (.sib 4 none 0 (.d32 0xc7))).toInstrSpec (mov_r64_m64_effect_step 0x121750 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x121758 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x121758 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121758 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121758 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121758 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x121758 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x12175d [0x48, 0x8B, 0x84, 0x24, 0xCF, 0x00, 0x00, 0x00] (LoadPre 0x12175d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcf)) s (0x12175d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12175d 0 (.sib 4 none 0 (.d32 0xcf)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12175d 0 (.sib 4 none 0 (.d32 0xcf))).toInstrSpec (mov_r64_m64_effect_step 0x12175d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xcf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x121765 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x121765 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x121765 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121765 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121765 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x121765 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x12176a [0xB0, 0x04] (fun s => s.RIP = 0x12176a) (movR8Imm8Effect 0x12176a 2 0 0x4)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x12176a 2 0 0x4).toInstrSpec (mov_r8_imm8_effect_step 0x12176a 0xb0 (by decide) 0x4) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12170a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121712) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121717) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12171c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121724) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121729) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121731) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121736) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12173e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121746) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 65), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12174b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121750) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121758) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12175d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121765) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 74), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12176a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12176c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 79) (by decide) rfl

theorem block_l121702 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121702 :=
  Rest.liftedBlock (rest_l121702 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121702 x hx)

theorem rest_l12176c_1 [Bindings] (code : CodeMap) :
    Rest (n := 81) code lifted (codeRange 0x12176c bytes_l12176c) [(0, 75), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      8 0x1217f2 bytes_l12176c_1 b_l12176c_1 := by
  have f20 : InstrSpec 0x1217f2 [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1217f2 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1217f2 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1217f2 (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1217f2 (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1217f2 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x1217fb [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1217fb 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1217fb + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1217fb (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1217fb (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1217fb 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x121804 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121804 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x121804 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x121804 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x121804 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x121804 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x12180d [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x12180d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12180d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x12180d (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x12180d (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x12180d 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x121816 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121816 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x121816 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x121816 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x121816 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x121816 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x12181f [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x12181f 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12181f + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x12181f (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x12181f (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x12181f 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x121828 [0x41, 0x8B, 0x7E, 0x50] (LoadPre 0x121828 (fun s => AddrMode.addr (.base 14 (.d8 0x50)) s (0x121828 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x121828 7 (.base 14 (.d8 0x50)))
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR32M32Effect_footprint 0x121828 7 (.base 14 (.d8 0x50))).toInstrSpec (mov_r32_m32_effect_step 0x121828 0x41 (by decide) 7 (.base 14 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x12182c [0xE8, 0x1F, 0x65, 0x00, 0x00] (PushPre 0x12182c 5) (callEffect (fun _ => 0x127d50) 0x121831)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12182c 0x127d50 0x121831).toInstrSpec (call_rel32_effect_step 0x12182c 0x651f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 75), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1217fb) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 75), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121804) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 75), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12180d) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 75), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121816) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 75), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12181f) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 75), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121828) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f26 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 75), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12182c) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f27 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 75), (1, 68), (2, 2), (3, 3), (4, 89), (5, 5), (6, 6), (7, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f27 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 91) (by decide) (by decide) rfl rfl

theorem rest_l12176c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12176c bytes_l12176c) (entryMap (live .l12176c))
      28 0x12176c bytes_l12176c b_l12176c := by
  have f0 : InstrSpec 0x12176c [0x88, 0x84, 0x24, 0xD7, 0x00, 0x00, 0x00] (StorePre 0x12176c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd7)) s (0x12176c + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x12176c 7 0 (.sib 4 none 0 (.d32 0xd7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x12176c 7 0 (.sib 4 none 0 (.d32 0xd7))).toInstrSpec (mov_m8_r8_effect_step 0x12176c 0 (by decide) (.sib 4 none 0 (.d32 0xd7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x121773 [0x48, 0x8B, 0x44, 0x24, 0x50] (LoadPre 0x121773 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x121773 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121773 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x121773 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x121773 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x121778 [0x48, 0x8B, 0x4C, 0x24, 0x58] (LoadPre 0x121778 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x121778 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121778 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x121778 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x121778 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12177d [0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x12177d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x12177d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12177d 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12177d 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x12177d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x121785 [0x48, 0x89, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x121785 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x121785 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x121785 1 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121785 1 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x121785 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12178d [0x48, 0x8B, 0x44, 0x24, 0x60] (LoadPre 0x12178d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12178d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12178d 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12178d 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x12178d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x121792 [0x48, 0x89, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00] (StorePre 0x121792 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x121792 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x121792 0 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121792 0 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x121792 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x12179a [0x48, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x12179a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x12179a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12179a 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12179a 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x12179a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x12179f [0x48, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00] (StorePre 0x12179f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x12179f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12179f 0 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12179f 0 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x12179f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1217a7 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x1217a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1217a7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1217a7 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1217a7 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1217a7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1217ac [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x1217ac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1217ac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1217ac 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1217ac 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1217ac 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1217b1 [0x48, 0x89, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00] (StorePre 0x1217b1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x1217b1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1217b1 0 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1217b1 0 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x1217b1 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1217b9 [0x48, 0x89, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x1217b9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x1217b9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1217b9 1 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1217b9 1 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m64_r64_effect_step 0x1217b9 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1217c1 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x1217c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1217c1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1217c1 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1217c1 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1217c1 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1217c6 [0x48, 0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x1217c6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1217c6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1217c6 0 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1217c6 0 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m64_r64_effect_step 0x1217c6 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1217ce [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x1217ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1217ce + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1217ce 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1217ce 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1217ce 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x1217d3 [0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x1217d3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x1217d3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1217d3 0 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1217d3 0 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m64_r64_effect_step 0x1217d3 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x1217db [0xC6, 0x44, 0x24, 0x48, 0x00] (StorePre 0x1217db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1217db + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1217db (.sib 4 none 0 (.d8 0x48)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1217db (.sib 4 none 0 (.d8 0x48)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1217db (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1217e0 [0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1217e0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1217e0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1217e0 (.sib 4 none 0 (.d8 0x40)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1217e0 (.sib 4 none 0 (.d8 0x40)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1217e0 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1217e9 [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1217e9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1217e9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1217e9 (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1217e9 (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1217e9 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121773) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121778) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12177d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 54), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121785) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 54), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12178d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121792) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 60), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12179a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12179f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1217a7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1217ac) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 66), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1217b1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 66), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1217b9) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 66), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1217c1) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1217c6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1217ce) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1217d3) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1217db) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 75), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1217e0) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 75), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1217e9) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 75), (1, 68), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1217f2) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l12176c_1 code

theorem block_l12176c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12176c :=
  Rest.liftedBlock (rest_l12176c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12176c x hx)

theorem rest_l121831 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121831 bytes_l121831) (entryMap (live .l121831))
      12 0x121831 bytes_l121831 b_l121831 := by
  have f0 : InstrSpec 0x121831 [0xC6, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121831 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x121831 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x121831 (.sib 4 none 0 (.d32 0x90)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x121831 (.sib 4 none 0 (.d32 0x90)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x121831 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x121839 [0x48, 0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121839 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x121839 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x121839 (.sib 4 none 0 (.d32 0x88)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x121839 (.sib 4 none 0 (.d32 0x88)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x121839 0x48 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x121845 [0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121845 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x121845 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x121845 (.sib 4 none 0 (.d32 0x80)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x121845 (.sib 4 none 0 (.d32 0x80)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x121845 0x48 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x121851 [0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121851 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x121851 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x121851 (.sib 4 none 0 (.d8 0x78)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x121851 (.sib 4 none 0 (.d8 0x78)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x121851 0x48 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12185a [0x48, 0xC7, 0x44, 0x24, 0x70, 0x00, 0x00, 0x00, 0x00] (StorePre 0x12185a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x12185a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x12185a (.sib 4 none 0 (.d8 0x70)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x12185a (.sib 4 none 0 (.d8 0x70)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x12185a 0x48 (by decide) (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x121863 [0x48, 0xC7, 0x44, 0x24, 0x68, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121863 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x121863 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x121863 (.sib 4 none 0 (.d8 0x68)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x121863 (.sib 4 none 0 (.d8 0x68)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x121863 0x48 (by decide) (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x12186c [0x48, 0xC7, 0x44, 0x24, 0x60, 0x00, 0x00, 0x00, 0x00] (StorePre 0x12186c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12186c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x12186c (.sib 4 none 0 (.d8 0x60)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x12186c (.sib 4 none 0 (.d8 0x60)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x12186c 0x48 (by decide) (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x121875 [0x48, 0xC7, 0x44, 0x24, 0x58, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121875 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x121875 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x121875 (.sib 4 none 0 (.d8 0x58)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x121875 (.sib 4 none 0 (.d8 0x58)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x121875 0x48 (by decide) (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x12187e [0x48, 0xC7, 0x44, 0x24, 0x50, 0x00, 0x00, 0x00, 0x00] (StorePre 0x12187e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x12187e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x12187e (.sib 4 none 0 (.d8 0x50)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x12187e (.sib 4 none 0 (.d8 0x50)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x12187e 0x48 (by decide) (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x121887 [0x31, 0xD2] (fun s => s.RIP = 0x121887) (xorR32R32Effect 0x121887 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x121887 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x121887 0xd2 (by decide)) pre_rip
  have f10 : InstrSpec 0x121889 [0x48, 0x8D, 0x4C, 0x24, 0x07] (fun s => s.RIP = 0x121889) (leaR64Effect 0x121889 1 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x121889 1 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x121889 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12188e [0x66, 0x90] (fun s => s.RIP = 0x12188e) (fun _ => nopEffect 0x12188e 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12188e 2).toInstrSpec (nop_66_effect_step 0x12188e) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121839) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121845) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121851) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12185a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121863) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12186c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121875) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12187e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121887) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (2, 62), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121889) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (2, 62), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12188e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (2, 62), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121890) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 66) (by decide) rfl

theorem block_l121831 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121831 :=
  Rest.liftedBlock (rest_l121831 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121831 x hx)

theorem rest_l121890 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121890 bytes_l121890) (entryMap (live .l121890))
      10 0x121890 bytes_l121890 b_l121890 := by
  have f0 : InstrSpec 0x121890 [0x0F, 0xB6, 0xB4, 0x14, 0xD7, 0x00, 0x00, 0x00] (LoadPre 0x121890 (fun s => AddrMode.addr (.sib 4 (some 2) 0 (.d32 0xd7)) s (0x121890 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x121890 8 6 (.sib 4 (some 2) 0 (.d32 0xd7)))
      [.gpr 4, .gpr 2] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x121890 8 6 (.sib 4 (some 2) 0 (.d32 0xd7))).toInstrSpec (movzx_r32_m8_effect_step 0x121890 6 (.sib 4 (some 2) 0 (.d32 0xd7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x121898 [0x88, 0x44, 0x24, 0x07] (StorePre 0x121898 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x121898 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x121898 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x121898 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x121898 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12189c [0x0F, 0xB6, 0x7C, 0x14, 0x08] (LoadPre 0x12189c (fun s => AddrMode.addr (.sib 4 (some 2) 0 (.d8 0x8)) s (0x12189c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x12189c 5 7 (.sib 4 (some 2) 0 (.d8 0x8)))
      [.gpr 4, .gpr 2] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x12189c 5 7 (.sib 4 (some 2) 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x12189c 7 (.sib 4 (some 2) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1218a1 [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x07] (LoadPre 0x1218a1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1218a1 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1218a1 6 8 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x1218a1 6 8 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1218a1 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1218a7 [0x45, 0x84, 0xC0] (fun s => s.RIP = 0x1218a7) (testR8R8Effect 0x1218a7 3 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1218a7 3 8 8).toInstrSpec (test_r8_r8_rex_effect_step 0x1218a7 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1218aa [0x0F, 0x45, 0xF7] (fun s => s.RIP = 0x1218aa) (atFlags (condHolds 5) (cmovR32R32Effect 0x1218aa 3 6 7))
      [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 6, .rip] :=
    (cmovR32R32Effect_footprint 0x1218aa 3 6 7 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_effect_step 0x1218aa 5 0xf7 (by decide) c)) pre_rip
  have f6 : InstrSpec 0x1218ad [0x40, 0x88, 0x74, 0x14, 0x50] (StorePre 0x1218ad 5 (fun s => AddrMode.addr (.sib 4 (some 2) 0 (.d8 0x50)) s (0x1218ad + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1218ad 5 6 (.sib 4 (some 2) 0 (.d8 0x50)))
      [.gpr 6, .gpr 4, .gpr 2] [] [.rip] :=
    (movM8R8Effect_footprint 0x1218ad 5 6 (.sib 4 (some 2) 0 (.d8 0x50))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1218ad 0x40 (by decide) 6 (.sib 4 (some 2) 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1218b2 [0x48, 0xFF, 0xC2] (fun s => s.RIP = 0x1218b2) (incR64Effect 0x1218b2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (incR64Effect_footprint 0x1218b2 2).toInstrSpec (inc_r64_effect_step 0x1218b2 0x48 0xc2 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1218b5 [0x48, 0x83, 0xFA, 0x41] (fun s => s.RIP = 0x1218b5) (cmpR64Imm8Effect 0x1218b5 2 0x41)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1218b5 2 0x41).toInstrSpec (cmp_r64_imm8_effect_step 0x1218b5 0x48 0xfa 0x41 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121898) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12189c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 56), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218a1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218a7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218aa) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 62), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218ad) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 62), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218b2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (2, 65), (3, 3), (4, 4), (5, 5), (6, 62), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218b5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (2, 65), (3, 3), (4, 4), (5, 5), (6, 62), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218b9) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 69) (jcc_rel8_effect_step 0x1218b9 5 0xd5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l121890 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121890 :=
  Rest.liftedBlock (rest_l121890 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121890 x hx)

theorem rest_l1218bb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1218bb bytes_l1218bb) (entryMap (live .l1218bb))
      4 0x1218bb bytes_l1218bb b_l1218bb := by
  have f0 : InstrSpec 0x1218bb [0x48, 0x8D, 0x74, 0x24, 0x50] (fun s => s.RIP = 0x1218bb) (leaR64Effect 0x1218bb 6 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1218bb 6 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x1218bb 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1218c0 [0xBA, 0x41, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1218c0) (movR32Imm32Effect 0x1218c0 5 2 0x41)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1218c0 5 2 0x41).toInstrSpec (mov_r32_imm32_effect_step 0x1218c0 0xba (by decide) 0x41) pre_rip
  have f2 : InstrSpec 0x1218c5 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x1218c5) (movR64R64Effect 0x1218c5 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1218c5 7 3).toInstrSpec (mov_r64_r64_effect_step 0x1218c5 0x48 0xdf (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1218c8 [0xFF, 0x15, 0x02, 0x25, 0x0E, 0x00] (GoesTo (CallMemPre 0x1218c8 (.rip 0xe2502)) (callEffect (callMemPtr 0x1218c8 (.rip 0xe2502)) (0x1218c8 + BitVec.ofNat 64 (callMemLen (.rip 0xe2502)))) 0x12a820) (callEffect (callMemPtr 0x1218c8 (.rip 0xe2502)) (0x1218c8 + BitVec.ofNat 64 (callMemLen (.rip 0xe2502))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1218c8 (.rip 0xe2502)).toInstrSpec (call_m64_effect_step 0x1218c8 (.rip 0xe2502) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218c0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218c5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218c8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 59), (5, 5), (6, 53), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1218bb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1218bb :=
  Rest.liftedBlock (rest_l1218bb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1218bb x hx)

theorem rest_l1218ce [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1218ce bytes_l1218ce) (entryMap (live .l1218ce))
      7 0x1218ce bytes_l1218ce b_l1218ce := by
  have f0 : InstrSpec 0x1218ce [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1218ce) (movR64R64Effect 0x1218ce 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1218ce 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1218ce 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1218d1 [0x48, 0x81, 0xC4, 0x18, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1218d1) (addR64Imm32Effect 0x1218d1 4 0x118)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x1218d1 4 0x118).toInstrSpec (add_r64_imm32_effect_step 0x1218d1 0x48 0xc4 0x118 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1218d8 [0x5B] (PopPre 0x1218d8) (popR64Effect 0x1218d8 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1218d8 1 3).toInstrSpec (pop_r64_effect_step 0x1218d8 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1218d9 [0x41, 0x5E] (PopPre 0x1218d9) (popR64Effect 0x1218d9 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1218d9 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1218d9 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1218db [0x41, 0x5F] (PopPre 0x1218db) (popR64Effect 0x1218db 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1218db 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1218db 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1218dd [0x5D] (PopPre 0x1218dd) (popR64Effect 0x1218dd 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1218dd 1 5).toInstrSpec (pop_r64_effect_step 0x1218dd 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1218de [0xC3] (RetPre 0x1218de) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1218de).toInstrSpec (ret_effect_step 0x1218de) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218d1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218d8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218d9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218db) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218dd) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (5, 66), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218de) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (5, 66), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) f6 (by decide) rfl rfl rfl (by decide)

theorem block_l1218ce [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1218ce :=
  Rest.liftedBlock (rest_l1218ce code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1218ce x hx)

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

theorem_by block_l1215e0_eval :
    program.runBlock (dialect code) ⟨.l1215e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121633_eval :
    program.runBlock (dialect code) ⟨.l121633, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121643_eval :
    program.runBlock (dialect code) ⟨.l121643, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121682_eval :
    program.runBlock (dialect code) ⟨.l121682, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121692_eval :
    program.runBlock (dialect code) ⟨.l121692, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121696_eval :
    program.runBlock (dialect code) ⟨.l121696, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1216a8_eval :
    program.runBlock (dialect code) ⟨.l1216a8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121702_eval :
    program.runBlock (dialect code) ⟨.l121702, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12176c_eval :
    program.runBlock (dialect code) ⟨.l12176c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121831_eval :
    program.runBlock (dialect code) ⟨.l121831, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121890_eval :
    program.runBlock (dialect code) ⟨.l121890, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1218bb_eval :
    program.runBlock (dialect code) ⟨.l1218bb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1218ce_eval :
    program.runBlock (dialect code) ⟨.l1218ce, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Ecdh.LIR
