import K256.Proofs.Signing.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Signing.LIR.Generated.Values

namespace K256.Proofs.Signing.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR K256.Proofs.Verify.LIR

theorem rest_l124de0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124de0 bytes_l124de0) (entryMap (live .l124de0))
      10 0x124de0 bytes_l124de0 b_l124de0 := by
  have f0 : InstrSpec 0x124de0 [0x55] (PushPre 0x124de0 1) (pushR64Effect 0x124de0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124de0 1 5).toInstrSpec (push_r64_effect_step 0x124de0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x124de1 [0x41, 0x57] (PushPre 0x124de1 2) (pushR64Effect 0x124de1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124de1 2 15).toInstrSpec (push_r64_rex_effect_step 0x124de1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x124de3 [0x41, 0x56] (PushPre 0x124de3 2) (pushR64Effect 0x124de3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124de3 2 14).toInstrSpec (push_r64_rex_effect_step 0x124de3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x124de5 [0x41, 0x54] (PushPre 0x124de5 2) (pushR64Effect 0x124de5 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124de5 2 12).toInstrSpec (push_r64_rex_effect_step 0x124de5 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x124de7 [0x53] (PushPre 0x124de7 1) (pushR64Effect 0x124de7 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124de7 1 3).toInstrSpec (push_r64_effect_step 0x124de7 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x124de8 [0x48, 0x81, 0xEC, 0xD0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x124de8) (subR64Imm32Effect 0x124de8 4 0xd0)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x124de8 4 0xd0).toInstrSpec (sub_r64_imm32_effect_step 0x124de8 0x48 0xec 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x124def [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x124def) (movR64R64Effect 0x124def 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x124def 14 6).toInstrSpec (mov_r64_r64_effect_step 0x124def 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x124df2 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x124df2) (movR64R64Effect 0x124df2 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x124df2 3 7).toInstrSpec (mov_r64_r64_effect_step 0x124df2 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x124df5 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x124df5) (movR64R64Effect 0x124df5 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x124df5 7 4).toInstrSpec (mov_r64_r64_effect_step 0x124df5 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x124df8 [0xE8, 0x53, 0x06, 0x00, 0x00] (PushPre 0x124df8 5) (callEffect (fun _ => 0x125450) 0x124dfd)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124df8 0x125450 0x124dfd).toInstrSpec (call_rel32_effect_step 0x124df8 0x653 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124de1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124de3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124de5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124de7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124de8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124def) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124df2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124df5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(3, 67), (4, 63), (5, 5), (6, 6), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124df8) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(3, 67), (4, 71), (5, 5), (6, 6), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125450) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l124de0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124de0 :=
  Rest.liftedBlock (rest_l124de0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124de0 x hx)

theorem rest_l124dfd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124dfd bytes_l124dfd) (entryMap (live .l124dfd))
      7 0x124dfd bytes_l124dfd b_l124dfd := by
  have f0 : InstrSpec 0x124dfd [0x8B, 0x04, 0x24] (LoadPre 0x124dfd (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124dfd + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124dfd 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x124dfd 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x124dfd 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124e00 [0x48, 0x8B, 0x4C, 0x24, 0x04] (LoadPre 0x124e00 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x124e00 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124e00 1 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124e00 1 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r64_m64_effect_step 0x124e00 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124e05 [0x48, 0x89, 0x4C, 0x24, 0x38] (StorePre 0x124e05 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124e05 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124e05 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124e05 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x124e05 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x124e0a [0x48, 0x8B, 0x4C, 0x24, 0x0C] (LoadPre 0x124e0a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x124e0a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124e0a 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124e0a 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r64_m64_effect_step 0x124e0a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x124e0f [0x48, 0x89, 0x4C, 0x24, 0x40] (StorePre 0x124e0f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124e0f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124e0f 1 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124e0f 1 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x124e0f 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x124e14 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x124e14) (cmpR32Imm8Effect 0x124e14 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124e14 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124e14 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e00) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e05) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e0a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e0f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e14) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e17) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel32_effect_step 0x124e17 5 0x19e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124dfd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124dfd :=
  Rest.liftedBlock (rest_l124dfd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124dfd x hx)

theorem rest_l124e1d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124e1d bytes_l124e1d) (entryMap (live .l124e1d))
      7 0x124e1d bytes_l124e1d b_l124e1d := by
  have f0 : InstrSpec 0x124e1d [0x48, 0x8B, 0x74, 0x24, 0x38] (LoadPre 0x124e1d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124e1d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124e1d 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124e1d 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x124e1d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124e22 [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x124e22 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124e22 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124e22 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x124e22 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x124e22 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124e27 [0x48, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x124e27 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x124e27 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124e27 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124e27 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x124e27 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x124e2f [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x124e2f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x124e2f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124e2f 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124e2f 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x124e2f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x124e37 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x124e37) (movR64R64Effect 0x124e37 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x124e37 7 4).toInstrSpec (mov_r64_r64_effect_step 0x124e37 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x124e3a [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x124e3a) (movR32Imm32Effect 0x124e3a 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x124e3a 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x124e3a 0xba (by decide) 0x1) pre_rip
  have f6 : InstrSpec 0x124e3f [0xE8, 0x8C, 0x28, 0x00, 0x00] (PushPre 0x124e3f 5) (callEffect (fun _ => 0x1276d0) 0x124e44)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124e3f 0x1276d0 0x124e44).toInstrSpec (call_rel32_effect_step 0x124e3f 0x288c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e22) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e27) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e2f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e37) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e3a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e3f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 63), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276d0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l124e1d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124e1d :=
  Rest.liftedBlock (rest_l124e1d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124e1d x hx)

theorem rest_l124e44 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124e44 bytes_l124e44) (entryMap (live .l124e44))
      3 0x124e44 bytes_l124e44 b_l124e44 := by
  have f0 : InstrSpec 0x124e44 [0x8B, 0x04, 0x24] (LoadPre 0x124e44 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124e44 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124e44 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x124e44 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x124e44 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124e47 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x124e47) (cmpR32Imm8Effect 0x124e47 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124e47 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124e47 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e47) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e4a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x124e4a 5 0x1b1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124e44 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124e44 :=
  Rest.liftedBlock (rest_l124e44 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124e44 x hx)

theorem rest_l124e50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124e50 bytes_l124e50) (entryMap (live .l124e50))
      4 0x124e50 bytes_l124e50 b_l124e50 := by
  have f0 : InstrSpec 0x124e50 [0x48, 0x8D, 0x7C, 0x24, 0x48] (fun s => s.RIP = 0x124e50) (leaR64Effect 0x124e50 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x124e50 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x124e50 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124e55 [0x48, 0x8D, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x124e55) (leaR64Effect 0x124e55 2 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x124e55 2 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (lea_r64_effect_step 0x124e55 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124e5d [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x124e5d) (movR64R64Effect 0x124e5d 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x124e5d 6 14).toInstrSpec (mov_r64_r64_effect_step 0x124e5d 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x124e60 [0xE8, 0x5B, 0x25, 0x00, 0x00] (PushPre 0x124e60 5) (callEffect (fun _ => 0x1273c0) 0x124e65)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124e60 0x1273c0 0x124e65).toInstrSpec (call_rel32_effect_step 0x124e60 0x255b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e55) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e5d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e60) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1273c0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l124e50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124e50 :=
  Rest.liftedBlock (rest_l124e50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124e50 x hx)

theorem rest_l124e65 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124e65 bytes_l124e65) (entryMap (live .l124e65))
      3 0x124e65 bytes_l124e65 b_l124e65 := by
  have f0 : InstrSpec 0x124e65 [0x8B, 0x44, 0x24, 0x48] (LoadPre 0x124e65 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x124e65 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124e65 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x124e65 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r32_m32_low_effect_step 0x124e65 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124e69 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x124e69) (cmpR32Imm8Effect 0x124e69 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124e69 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124e69 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e69) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e6c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x124e6c 5 0x1d3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124e65 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124e65 :=
  Rest.liftedBlock (rest_l124e65 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124e65 x hx)

theorem rest_l124e72 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124e72 bytes_l124e72) (entryMap (live .l124e72))
      2 0x124e72 bytes_l124e72 b_l124e72 := by
  have f0 : InstrSpec 0x124e72 [0x80, 0x7C, 0x24, 0x4C, 0x01] (LoadPre 0x124e72 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x124e72 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x124e72 5 (.sib 4 none 0 (.d8 0x4c)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x124e72 5 (.sib 4 none 0 (.d8 0x4c)) 0x1).toInstrSpec (cmp_m8_imm8_effect_step 0x124e72 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e77) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x124e77 5 0x22b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124e72 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124e72 :=
  Rest.liftedBlock (rest_l124e72 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124e72 x hx)

theorem rest_l124e7d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124e7d bytes_l124e7d) (entryMap (live .l124e7d))
      3 0x124e7d bytes_l124e7d b_l124e7d := by
  have f0 : InstrSpec 0x124e7d [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x124e7d) (movR64R64Effect 0x124e7d 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x124e7d 7 4).toInstrSpec (mov_r64_r64_effect_step 0x124e7d 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124e80 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x124e80) (movR64R64Effect 0x124e80 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x124e80 6 14).toInstrSpec (mov_r64_r64_effect_step 0x124e80 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124e83 [0xE8, 0xC8, 0x05, 0x00, 0x00] (PushPre 0x124e83 5) (callEffect (fun _ => 0x125450) 0x124e88)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124e83 0x125450 0x124e88).toInstrSpec (call_rel32_effect_step 0x124e83 0x5c8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e80) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e83) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125450) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l124e7d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124e7d :=
  Rest.liftedBlock (rest_l124e7d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124e7d x hx)

theorem rest_l124e88 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124e88 bytes_l124e88) (entryMap (live .l124e88))
      7 0x124e88 bytes_l124e88 b_l124e88 := by
  have f0 : InstrSpec 0x124e88 [0x8B, 0x04, 0x24] (LoadPre 0x124e88 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124e88 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124e88 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x124e88 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x124e88 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124e8b [0x48, 0x8B, 0x4C, 0x24, 0x04] (LoadPre 0x124e8b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x124e8b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124e8b 1 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124e8b 1 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r64_m64_effect_step 0x124e8b 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124e90 [0x48, 0x89, 0x4C, 0x24, 0x38] (StorePre 0x124e90 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124e90 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124e90 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124e90 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x124e90 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x124e95 [0x48, 0x8B, 0x4C, 0x24, 0x0C] (LoadPre 0x124e95 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x124e95 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124e95 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124e95 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r64_m64_effect_step 0x124e95 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x124e9a [0x48, 0x89, 0x4C, 0x24, 0x40] (StorePre 0x124e9a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124e9a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124e9a 1 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124e9a 1 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x124e9a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x124e9f [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x124e9f) (cmpR32Imm8Effect 0x124e9f 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124e9f 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124e9f 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e8b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e90) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e95) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e9a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124e9f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ea2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel32_effect_step 0x124ea2 5 0x21d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124e88 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124e88 :=
  Rest.liftedBlock (rest_l124e88 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124e88 x hx)

theorem rest_l124ea8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124ea8 bytes_l124ea8) (entryMap (live .l124ea8))
      7 0x124ea8 bytes_l124ea8 b_l124ea8 := by
  have f0 : InstrSpec 0x124ea8 [0x48, 0x8B, 0x74, 0x24, 0x38] (LoadPre 0x124ea8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124ea8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124ea8 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124ea8 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x124ea8 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124ead [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x124ead (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124ead + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124ead 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x124ead 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x124ead 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124eb2 [0x48, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x124eb2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x124eb2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124eb2 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124eb2 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x124eb2 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x124eba [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x124eba 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x124eba + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124eba 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124eba 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x124eba 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x124ec2 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x124ec2) (movR64R64Effect 0x124ec2 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x124ec2 7 4).toInstrSpec (mov_r64_r64_effect_step 0x124ec2 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x124ec5 [0xBA, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x124ec5) (movR32Imm32Effect 0x124ec5 5 2 0x3)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x124ec5 5 2 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x124ec5 0xba (by decide) 0x3) pre_rip
  have f6 : InstrSpec 0x124eca [0xE8, 0x01, 0x28, 0x00, 0x00] (PushPre 0x124eca 5) (callEffect (fun _ => 0x1276d0) 0x124ecf)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124eca 0x1276d0 0x124ecf).toInstrSpec (call_rel32_effect_step 0x124eca 0x2801 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ead) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124eb2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124eba) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ec2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ec5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124eca) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 63), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276d0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l124ea8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124ea8 :=
  Rest.liftedBlock (rest_l124ea8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124ea8 x hx)

theorem rest_l124ecf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124ecf bytes_l124ecf) (entryMap (live .l124ecf))
      3 0x124ecf bytes_l124ecf b_l124ecf := by
  have f0 : InstrSpec 0x124ecf [0x8B, 0x04, 0x24] (LoadPre 0x124ecf (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124ecf + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124ecf 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x124ecf 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x124ecf 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124ed2 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x124ed2) (cmpR32Imm8Effect 0x124ed2 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124ed2 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124ed2 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ed2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ed5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x124ed5 5 0x230) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124ecf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124ecf :=
  Rest.liftedBlock (rest_l124ecf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124ecf x hx)

theorem rest_l124edb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124edb bytes_l124edb) (entryMap (live .l124edb))
      4 0x124edb bytes_l124edb b_l124edb := by
  have f0 : InstrSpec 0x124edb [0x48, 0x8D, 0x7C, 0x24, 0x48] (fun s => s.RIP = 0x124edb) (leaR64Effect 0x124edb 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x124edb 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x124edb 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124ee0 [0x48, 0x8D, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x124ee0) (leaR64Effect 0x124ee0 2 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x124ee0 2 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (lea_r64_effect_step 0x124ee0 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124ee8 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x124ee8) (movR64R64Effect 0x124ee8 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x124ee8 6 14).toInstrSpec (mov_r64_r64_effect_step 0x124ee8 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x124eeb [0xE8, 0x60, 0x22, 0x00, 0x00] (PushPre 0x124eeb 5) (callEffect (fun _ => 0x127150) 0x124ef0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124eeb 0x127150 0x124ef0).toInstrSpec (call_rel32_effect_step 0x124eeb 0x2260 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ee0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ee8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124eeb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127150) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l124edb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124edb :=
  Rest.liftedBlock (rest_l124edb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124edb x hx)

theorem rest_l124ef0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124ef0 bytes_l124ef0) (entryMap (live .l124ef0))
      3 0x124ef0 bytes_l124ef0 b_l124ef0 := by
  have f0 : InstrSpec 0x124ef0 [0x8B, 0x44, 0x24, 0x48] (LoadPre 0x124ef0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x124ef0 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124ef0 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x124ef0 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r32_m32_low_effect_step 0x124ef0 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124ef4 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x124ef4) (cmpR32Imm8Effect 0x124ef4 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124ef4 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124ef4 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ef4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ef7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x124ef7 5 0x252) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124ef0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124ef0 :=
  Rest.liftedBlock (rest_l124ef0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124ef0 x hx)

theorem rest_l124efd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124efd bytes_l124efd) (entryMap (live .l124efd))
      6 0x124efd bytes_l124efd b_l124efd := by
  have f0 : InstrSpec 0x124efd [0x4C, 0x8B, 0x7C, 0x24, 0x50] (LoadPre 0x124efd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x124efd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124efd 15 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x124efd 15 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x124efd 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124f02 [0x4C, 0x8B, 0x64, 0x24, 0x58] (LoadPre 0x124f02 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x124f02 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124f02 12 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x124f02 12 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x124f02 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124f07 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x124f07) (movR64R64Effect 0x124f07 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x124f07 7 4).toInstrSpec (mov_r64_r64_effect_step 0x124f07 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x124f0a [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x124f0a) (movR64R64Effect 0x124f0a 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x124f0a 6 14).toInstrSpec (mov_r64_r64_effect_step 0x124f0a 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x124f0d [0x31, 0xD2] (fun s => s.RIP = 0x124f0d) (xorR32R32Effect 0x124f0d 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x124f0d 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x124f0d 0xd2 (by decide)) pre_rip
  have f5 : InstrSpec 0x124f0f [0xE8, 0xCC, 0x13, 0x00, 0x00] (PushPre 0x124f0f 5) (callEffect (fun _ => 0x1262e0) 0x124f14)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124f0f 0x1262e0 0x124f14).toInstrSpec (call_rel32_effect_step 0x124f0f 0x13cc (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f02) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f07) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f0a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f0d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f0f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 61), (3, 3), (4, 63), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262e0) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l124efd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124efd :=
  Rest.liftedBlock (rest_l124efd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124efd x hx)

theorem rest_l124f14 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124f14 bytes_l124f14) (entryMap (live .l124f14))
      3 0x124f14 bytes_l124f14 b_l124f14 := by
  have f0 : InstrSpec 0x124f14 [0x8B, 0x04, 0x24] (LoadPre 0x124f14 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124f14 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124f14 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x124f14 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x124f14 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124f17 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x124f17) (cmpR32Imm8Effect 0x124f17 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124f17 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124f17 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f17) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f1a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x124f1a 5 0x274) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124f14 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124f14 :=
  Rest.liftedBlock (rest_l124f14 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124f14 x hx)

theorem rest_l124f20_1 [Bindings] (code : CodeMap) :
    Rest (n := 81) code lifted (codeRange 0x124f20 bytes_l124f20) [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x124f97 bytes_l124f20_1 b_l124f20_1 := by
  have f20 : InstrSpec 0x124f97 [0x0F, 0xB6, 0x44, 0x24, 0x3A] (LoadPre 0x124f97 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x124f97 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x124f97 5 0 (.sib 4 none 0 (.d8 0x3a)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x124f97 5 0 (.sib 4 none 0 (.d8 0x3a))).toInstrSpec (movzx_r32_m8_effect_step 0x124f97 0 (.sib 4 none 0 (.d8 0x3a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x124f9c [0x88, 0x44, 0x24, 0x72] (StorePre 0x124f9c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x124f9c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x124f9c 4 0 (.sib 4 none 0 (.d8 0x72)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x124f9c 4 0 (.sib 4 none 0 (.d8 0x72))).toInstrSpec (mov_m8_r8_effect_step 0x124f9c 0 (by decide) (.sib 4 none 0 (.d8 0x72)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x124fa0 [0x0F, 0xB7, 0x44, 0x24, 0x38] (LoadPre 0x124fa0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124fa0 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x124fa0 5 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x124fa0 5 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (movzx_r32_m16_effect_step 0x124fa0 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x124fa5 [0x66, 0x89, 0x44, 0x24, 0x70] (StorePre 0x124fa5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x124fa5 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x124fa5 5 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x124fa5 5 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m16_r16_effect_step 0x124fa5 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x124faa [0x41, 0x80, 0xF8, 0x02] (fun s => s.RIP = 0x124faa) (cmpR8Imm8Effect 0x124faa 4 8 0x2)
      [.gpr 8] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x124faa 4 8 0x2).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x124faa 0x41 0xf8 0x2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f9c) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 81), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124fa0) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 84), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124fa5) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 84), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124faa) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f24 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 84), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124fae) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 89) (jcc_rel32_effect_step 0x124fae 5 0x303) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l124f20 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124f20 bytes_l124f20) (entryMap (live .l124f20))
      26 0x124f20 bytes_l124f20 b_l124f20 := by
  have f0 : InstrSpec 0x124f20 [0x48, 0x8B, 0x44, 0x24, 0x25] (LoadPre 0x124f20 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x124f20 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124f20 0 (.sib 4 none 0 (.d8 0x25)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x124f20 0 (.sib 4 none 0 (.d8 0x25))).toInstrSpec (mov_r64_m64_effect_step 0x124f20 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124f25 [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x124f25 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x124f25 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124f25 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124f25 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x124f25 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x124f2d [0x48, 0x8B, 0x4C, 0x24, 0x1D] (LoadPre 0x124f2d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x124f2d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124f2d 1 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124f2d 1 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (mov_r64_m64_effect_step 0x124f2d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x124f32 [0x48, 0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x124f32 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x124f32 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124f32 1 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124f32 1 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x124f32 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x124f3a [0x48, 0x8B, 0x54, 0x24, 0x15] (LoadPre 0x124f3a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x124f3a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124f3a 2 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124f3a 2 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (mov_r64_m64_effect_step 0x124f3a 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x124f3f [0x48, 0x89, 0x94, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x124f3f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x124f3f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124f3f 2 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124f3f 2 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x124f3f 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x124f47 [0x48, 0x8B, 0x74, 0x24, 0x05] (LoadPre 0x124f47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5)) s (0x124f47 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124f47 6 (.sib 4 none 0 (.d8 0x5)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124f47 6 (.sib 4 none 0 (.d8 0x5))).toInstrSpec (mov_r64_m64_effect_step 0x124f47 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x124f4c [0x48, 0x8B, 0x7C, 0x24, 0x0D] (LoadPre 0x124f4c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x124f4c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124f4c 7 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x124f4c 7 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (mov_r64_m64_effect_step 0x124f4c 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x124f51 [0x48, 0x89, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x124f51 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x124f51 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124f51 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124f51 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x124f51 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x124f59 [0x48, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x124f59 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x124f59 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124f59 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124f59 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x124f59 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x124f61 [0x44, 0x0F, 0xB7, 0x44, 0x24, 0x2D] (LoadPre 0x124f61 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x124f61 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x124f61 6 8 (.sib 4 none 0 (.d8 0x2d)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M16Effect_footprint 0x124f61 6 8 (.sib 4 none 0 (.d8 0x2d))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x124f61 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x124f67 [0x66, 0x44, 0x89, 0x44, 0x24, 0x38] (StorePre 0x124f67 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124f67 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x124f67 6 8 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x124f67 6 8 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m16_r16_rex_effect_step 0x124f67 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x124f6d [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x2F] (LoadPre 0x124f6d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2f)) s (0x124f6d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x124f6d 6 8 (.sib 4 none 0 (.d8 0x2f)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x124f6d 6 8 (.sib 4 none 0 (.d8 0x2f))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x124f6d 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x2f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x124f73 [0x44, 0x88, 0x44, 0x24, 0x3A] (StorePre 0x124f73 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x124f73 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x124f73 5 8 (.sib 4 none 0 (.d8 0x3a)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x124f73 5 8 (.sib 4 none 0 (.d8 0x3a))).toInstrSpec (mov_m8_r8_rex_effect_step 0x124f73 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x3a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x124f78 [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x30] (LoadPre 0x124f78 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x124f78 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x124f78 6 8 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x124f78 6 8 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x124f78 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x124f7e [0x48, 0x89, 0x74, 0x24, 0x48] (StorePre 0x124f7e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x124f7e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124f7e 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124f7e 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x124f7e 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x124f83 [0x48, 0x89, 0x7C, 0x24, 0x50] (StorePre 0x124f83 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x124f83 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124f83 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124f83 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x124f83 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x124f88 [0x48, 0x89, 0x54, 0x24, 0x58] (StorePre 0x124f88 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x124f88 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124f88 2 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124f88 2 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x124f88 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x124f8d [0x48, 0x89, 0x4C, 0x24, 0x60] (StorePre 0x124f8d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x124f8d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124f8d 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124f8d 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x124f8d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x124f92 [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x124f92 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x124f92 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124f92 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124f92 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x124f92 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f25) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f2d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 56), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f32) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 56), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f3a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f3f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f47) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f4c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f51) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f59) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f61) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 68), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f67) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 68), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f6d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 71), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f73) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 71), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f78) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f7e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f83) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f88) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f8d) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f92) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124f97) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l124f20_1 code

theorem block_l124f20 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124f20 :=
  Rest.liftedBlock (rest_l124f20 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124f20 x hx)

theorem rest_l124fb4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124fb4 bytes_l124fb4) (entryMap (live .l124fb4))
      2 0x124fb4 bytes_l124fb4 b_l124fb4 := by
  have f0 : InstrSpec 0x124fb4 [0x31, 0xED] (fun s => s.RIP = 0x124fb4) (xorR32R32Effect 0x124fb4 2 5 5)
      [.gpr 5, .gpr 5] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x124fb4 2 5 5).toInstrSpec (xor_r32_r32_effect_step 0x124fb4 0xed (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124fb6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x124fb6 0x340 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124fb4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124fb4 :=
  Rest.liftedBlock (rest_l124fb4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124fb4 x hx)

theorem rest_l124fbb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124fbb bytes_l124fbb) (entryMap (live .l124fbb))
      15 0x124fbb bytes_l124fbb b_l124fbb := by
  have f0 : InstrSpec 0x124fbb [0x8B, 0x4C, 0x24, 0x34] (LoadPre 0x124fbb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x124fbb + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124fbb 1 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x124fbb 1 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r32_m32_low_effect_step 0x124fbb 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124fbf [0x89, 0x4C, 0x24, 0x7C] (StorePre 0x124fbf 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x124fbf + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x124fbf 1 (.sib 4 none 0 (.d8 0x7c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124fbf 1 (.sib 4 none 0 (.d8 0x7c))).toInstrSpec (mov_m32_r32_low_effect_step 0x124fbf 1 (.sib 4 none 0 (.d8 0x7c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x124fc3 [0x48, 0x8B, 0x4C, 0x24, 0x2C] (LoadPre 0x124fc3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x124fc3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124fc3 1 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124fc3 1 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x124fc3 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x124fc8 [0x48, 0x89, 0x4C, 0x24, 0x74] (StorePre 0x124fc8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x124fc8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124fc8 1 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124fc8 1 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (mov_m64_r64_effect_step 0x124fc8 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x124fcd [0x48, 0x8B, 0x4C, 0x24, 0x24] (LoadPre 0x124fcd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x124fcd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124fcd 1 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124fcd 1 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x124fcd 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x124fd2 [0x48, 0x89, 0x4C, 0x24, 0x6C] (StorePre 0x124fd2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x124fd2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124fd2 1 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124fd2 1 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (mov_m64_r64_effect_step 0x124fd2 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x124fd7 [0x48, 0x8B, 0x4C, 0x24, 0x14] (LoadPre 0x124fd7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124fd7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124fd7 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124fd7 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x124fd7 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x124fdc [0x48, 0x8B, 0x54, 0x24, 0x1C] (LoadPre 0x124fdc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x124fdc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124fdc 2 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124fdc 2 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x124fdc 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x124fe1 [0x48, 0x89, 0x54, 0x24, 0x64] (StorePre 0x124fe1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x124fe1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124fe1 2 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124fe1 2 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (mov_m64_r64_effect_step 0x124fe1 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x124fe6 [0x48, 0x89, 0x4C, 0x24, 0x5C] (StorePre 0x124fe6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x124fe6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124fe6 1 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124fe6 1 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (mov_m64_r64_effect_step 0x124fe6 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x124feb [0x48, 0x8B, 0x4C, 0x24, 0x38] (LoadPre 0x124feb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124feb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124feb 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124feb 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x124feb 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x124ff0 [0x48, 0x8B, 0x54, 0x24, 0x40] (LoadPre 0x124ff0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124ff0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124ff0 2 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124ff0 2 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x124ff0 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x124ff5 [0x48, 0x89, 0x4C, 0x24, 0x4C] (StorePre 0x124ff5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x124ff5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124ff5 1 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124ff5 1 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_m64_r64_effect_step 0x124ff5 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x124ffa [0x48, 0x89, 0x54, 0x24, 0x54] (StorePre 0x124ffa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x124ffa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124ffa 2 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124ffa 2 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_m64_r64_effect_step 0x124ffa 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124fbf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124fc3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124fc8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124fcd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124fd2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124fd7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 62), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124fdc) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124fe1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124fe6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124feb) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 68), (2, 64), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ff0) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ff5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ffa) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124fff) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 74) (jmp_rel8_effect_step 0x124fff 0x44 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124fbb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124fbb :=
  Rest.liftedBlock (rest_l124fbb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124fbb x hx)

theorem rest_l125001 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125001 bytes_l125001) (entryMap (live .l125001))
      14 0x125001 bytes_l125001 b_l125001 := by
  have f0 : InstrSpec 0x125001 [0x48, 0x8B, 0x4C, 0x24, 0x04] (LoadPre 0x125001 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x125001 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125001 1 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x125001 1 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r64_m64_effect_step 0x125001 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125006 [0x48, 0x8B, 0x54, 0x24, 0x0C] (LoadPre 0x125006 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x125006 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125006 2 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125006 2 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r64_m64_effect_step 0x125006 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12500b [0x48, 0x89, 0x54, 0x24, 0x54] (StorePre 0x12500b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x12500b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12500b 2 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12500b 2 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_m64_r64_effect_step 0x12500b 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x125010 [0x48, 0x8B, 0x54, 0x24, 0x14] (LoadPre 0x125010 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x125010 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125010 2 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125010 2 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x125010 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x125015 [0x48, 0x89, 0x54, 0x24, 0x5C] (StorePre 0x125015 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x125015 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125015 2 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125015 2 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (mov_m64_r64_effect_step 0x125015 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12501a [0x48, 0x8B, 0x54, 0x24, 0x1C] (LoadPre 0x12501a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x12501a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12501a 2 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12501a 2 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x12501a 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x12501f [0x48, 0x89, 0x54, 0x24, 0x64] (StorePre 0x12501f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x12501f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12501f 2 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12501f 2 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (mov_m64_r64_effect_step 0x12501f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x125024 [0x48, 0x8B, 0x54, 0x24, 0x24] (LoadPre 0x125024 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x125024 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125024 2 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125024 2 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x125024 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x125029 [0x48, 0x89, 0x54, 0x24, 0x6C] (StorePre 0x125029 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x125029 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125029 2 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125029 2 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (mov_m64_r64_effect_step 0x125029 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12502e [0x48, 0x8B, 0x54, 0x24, 0x2C] (LoadPre 0x12502e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x12502e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12502e 2 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12502e 2 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x12502e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x125033 [0x48, 0x89, 0x54, 0x24, 0x74] (StorePre 0x125033 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x125033 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125033 2 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125033 2 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (mov_m64_r64_effect_step 0x125033 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x125038 [0x8B, 0x54, 0x24, 0x34] (LoadPre 0x125038 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x125038 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125038 2 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x125038 2 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r32_m32_low_effect_step 0x125038 2 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x12503c [0x89, 0x54, 0x24, 0x7C] (StorePre 0x12503c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x12503c + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x12503c 2 (.sib 4 none 0 (.d8 0x7c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x12503c 2 (.sib 4 none 0 (.d8 0x7c))).toInstrSpec (mov_m32_r32_low_effect_step 0x12503c 2 (.sib 4 none 0 (.d8 0x7c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x125040 [0x48, 0x89, 0x4C, 0x24, 0x4C] (StorePre 0x125040 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x125040 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125040 1 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125040 1 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_m64_r64_effect_step 0x125040 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125006) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12500b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125010) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 53), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125015) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12501a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12501f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125024) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 53), (2, 64), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125029) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 64), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12502e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 53), (2, 67), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125033) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 53), (2, 67), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125038) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12503c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125040) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125045) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 74) (by decide) rfl

theorem block_l125001 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125001 :=
  Rest.liftedBlock (rest_l125001 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125001 x hx)

theorem rest_l125045 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125045 bytes_l125045) (entryMap (live .l125045))
      17 0x125045 bytes_l125045 b_l125045 := by
  have f0 : InstrSpec 0x125045 [0x0F, 0xB6, 0x4C, 0x24, 0x4C] (LoadPre 0x125045 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x125045 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125045 5 1 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x125045 5 1 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (movzx_r32_m8_effect_step 0x125045 1 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12504a [0x8B, 0x54, 0x24, 0x7C] (LoadPre 0x12504a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x12504a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12504a 2 (.sib 4 none 0 (.d8 0x7c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x12504a 2 (.sib 4 none 0 (.d8 0x7c))).toInstrSpec (mov_r32_m32_low_effect_step 0x12504a 2 (.sib 4 none 0 (.d8 0x7c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12504e [0x89, 0x53, 0x3C] (StorePre 0x12504e 3 (fun s => AddrMode.addr (.base 3 (.d8 0x3c)) s (0x12504e + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12504e 2 (.base 3 (.d8 0x3c)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x12504e 2 (.base 3 (.d8 0x3c))).toInstrSpec (mov_m32_r32_low_effect_step 0x12504e 2 (.base 3 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x125051 [0x48, 0x8B, 0x54, 0x24, 0x75] (LoadPre 0x125051 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x75)) s (0x125051 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125051 2 (.sib 4 none 0 (.d8 0x75)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125051 2 (.sib 4 none 0 (.d8 0x75))).toInstrSpec (mov_r64_m64_effect_step 0x125051 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x75)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x125056 [0x48, 0x89, 0x53, 0x35] (StorePre 0x125056 4 (fun s => AddrMode.addr (.base 3 (.d8 0x35)) s (0x125056 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125056 2 (.base 3 (.d8 0x35)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125056 2 (.base 3 (.d8 0x35))).toInstrSpec (mov_m64_r64_effect_step 0x125056 0x48 (by decide) 2 (.base 3 (.d8 0x35)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12505a [0x48, 0x8B, 0x54, 0x24, 0x6D] (LoadPre 0x12505a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6d)) s (0x12505a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12505a 2 (.sib 4 none 0 (.d8 0x6d)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12505a 2 (.sib 4 none 0 (.d8 0x6d))).toInstrSpec (mov_r64_m64_effect_step 0x12505a 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x6d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x12505f [0x48, 0x89, 0x53, 0x2D] (StorePre 0x12505f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2d)) s (0x12505f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12505f 2 (.base 3 (.d8 0x2d)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12505f 2 (.base 3 (.d8 0x2d))).toInstrSpec (mov_m64_r64_effect_step 0x12505f 0x48 (by decide) 2 (.base 3 (.d8 0x2d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x125063 [0x48, 0x8B, 0x54, 0x24, 0x65] (LoadPre 0x125063 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x65)) s (0x125063 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125063 2 (.sib 4 none 0 (.d8 0x65)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125063 2 (.sib 4 none 0 (.d8 0x65))).toInstrSpec (mov_r64_m64_effect_step 0x125063 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x65)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x125068 [0x48, 0x89, 0x53, 0x25] (StorePre 0x125068 4 (fun s => AddrMode.addr (.base 3 (.d8 0x25)) s (0x125068 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125068 2 (.base 3 (.d8 0x25)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125068 2 (.base 3 (.d8 0x25))).toInstrSpec (mov_m64_r64_effect_step 0x125068 0x48 (by decide) 2 (.base 3 (.d8 0x25)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12506c [0x48, 0x8B, 0x54, 0x24, 0x5D] (LoadPre 0x12506c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5d)) s (0x12506c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12506c 2 (.sib 4 none 0 (.d8 0x5d)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12506c 2 (.sib 4 none 0 (.d8 0x5d))).toInstrSpec (mov_r64_m64_effect_step 0x12506c 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x5d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x125071 [0x48, 0x89, 0x53, 0x1D] (StorePre 0x125071 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1d)) s (0x125071 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125071 2 (.base 3 (.d8 0x1d)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125071 2 (.base 3 (.d8 0x1d))).toInstrSpec (mov_m64_r64_effect_step 0x125071 0x48 (by decide) 2 (.base 3 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x125075 [0x48, 0x8B, 0x54, 0x24, 0x55] (LoadPre 0x125075 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x55)) s (0x125075 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125075 2 (.sib 4 none 0 (.d8 0x55)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125075 2 (.sib 4 none 0 (.d8 0x55))).toInstrSpec (mov_r64_m64_effect_step 0x125075 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x55)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x12507a [0x48, 0x89, 0x53, 0x15] (StorePre 0x12507a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x12507a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12507a 2 (.base 3 (.d8 0x15)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12507a 2 (.base 3 (.d8 0x15))).toInstrSpec (mov_m64_r64_effect_step 0x12507a 0x48 (by decide) 2 (.base 3 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x12507e [0x48, 0x8B, 0x54, 0x24, 0x4D] (LoadPre 0x12507e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x12507e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12507e 2 (.sib 4 none 0 (.d8 0x4d)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12507e 2 (.sib 4 none 0 (.d8 0x4d))).toInstrSpec (mov_r64_m64_effect_step 0x12507e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x4d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x125083 [0x48, 0x89, 0x53, 0x0D] (StorePre 0x125083 4 (fun s => AddrMode.addr (.base 3 (.d8 0xd)) s (0x125083 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125083 2 (.base 3 (.d8 0xd)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125083 2 (.base 3 (.d8 0xd))).toInstrSpec (mov_m64_r64_effect_step 0x125083 0x48 (by decide) 2 (.base 3 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x125087 [0x89, 0x43, 0x08] (StorePre 0x125087 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x125087 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125087 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125087 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x125087 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x12508a [0x88, 0x4B, 0x0C] (StorePre 0x12508a 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x12508a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x12508a 3 1 (.base 3 (.d8 0xc)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x12508a 3 1 (.base 3 (.d8 0xc))).toInstrSpec (mov_m8_r8_effect_step 0x12508a 1 (by decide) (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12504a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12504e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125051) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 53), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125056) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12505a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12505f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125063) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 53), (2, 64), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125068) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 64), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12506c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 53), (2, 67), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125071) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 53), (2, 67), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125075) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12507a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12507e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 53), (2, 73), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125083) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 53), (2, 73), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125087) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 53), (2, 73), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12508a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 53), (2, 73), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12508d) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 78) (by decide) rfl

theorem block_l125045 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125045 :=
  Rest.liftedBlock (rest_l125045 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125045 x hx)

theorem rest_l12508d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12508d bytes_l12508d) (entryMap (live .l12508d))
      1 0x12508d bytes_l12508d b_l12508d := by
  have f0 : InstrSpec 0x12508d [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12508d) (movR32Imm32Effect 0x12508d 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x12508d 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x12508d 0xb8 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125092) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l12508d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12508d :=
  Rest.liftedBlock (rest_l12508d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12508d x hx)

theorem rest_l125092 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125092 bytes_l125092) (entryMap (live .l125092))
      9 0x125092 bytes_l125092 b_l125092 := by
  have f0 : InstrSpec 0x125092 [0x48, 0x89, 0x03] (StorePre 0x125092 3 (fun s => AddrMode.addr (.base 3 .none) s (0x125092 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x125092 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125092 0 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x125092 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x125095 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x125095) (movR64R64Effect 0x125095 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x125095 0 3).toInstrSpec (mov_r64_r64_effect_step 0x125095 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x125098 [0x48, 0x81, 0xC4, 0xD0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125098) (addR64Imm32Effect 0x125098 4 0xd0)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x125098 4 0xd0).toInstrSpec (add_r64_imm32_effect_step 0x125098 0x48 0xc4 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12509f [0x5B] (PopPre 0x12509f) (popR64Effect 0x12509f 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12509f 1 3).toInstrSpec (pop_r64_effect_step 0x12509f 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1250a0 [0x41, 0x5C] (PopPre 0x1250a0) (popR64Effect 0x1250a0 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1250a0 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1250a0 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1250a2 [0x41, 0x5E] (PopPre 0x1250a2) (popR64Effect 0x1250a2 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1250a2 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1250a2 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1250a4 [0x41, 0x5F] (PopPre 0x1250a4) (popR64Effect 0x1250a4 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1250a4 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1250a4 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1250a6 [0x5D] (PopPre 0x1250a6) (popR64Effect 0x1250a6 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1250a6 1 5).toInstrSpec (pop_r64_effect_step 0x1250a6 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x1250a7 [0xC3] (RetPre 0x1250a7) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1250a7).toInstrSpec (ret_effect_step 0x1250a7) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125095) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125098) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12509f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250a0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250a2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250a4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250a6) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250a7) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l125092 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125092 :=
  Rest.liftedBlock (rest_l125092 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125092 x hx)

theorem rest_l1250a8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1250a8 bytes_l1250a8) (entryMap (live .l1250a8))
      7 0x1250a8 bytes_l1250a8 b_l1250a8 := by
  have f0 : InstrSpec 0x1250a8 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x1250a8 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1250a8 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1250a8 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x1250a8 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x1250a8 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1250ad [0x41, 0x8B, 0x46, 0x1C] (LoadPre 0x1250ad (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1250ad + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1250ad 0 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR32M32Effect_footprint 0x1250ad 0 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x1250ad 0x41 (by decide) 0 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1250b1 [0xC7, 0x43, 0x08, 0x01, 0x00, 0x00, 0x00] (StorePre 0x1250b1 7 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1250b1 + BitVec.ofNat 64 7)) 4) (movM32Imm32Effect 0x1250b1 7 (.base 3 (.d8 0x8)) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1250b1 7 (.base 3 (.d8 0x8)) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x1250b1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1250b8 [0x89, 0x43, 0x0C] (StorePre 0x1250b8 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x1250b8 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1250b8 0 (.base 3 (.d8 0xc)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1250b8 0 (.base 3 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x1250b8 0 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1250bb [0xC6, 0x43, 0x10, 0x15] (StorePre 0x1250bb 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1250bb + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1250bb (.base 3 (.d8 0x10)) 0x15)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1250bb (.base 3 (.d8 0x10)) 0x15).toInstrSpec (mov_m8_imm8_effect_step 0x1250bb (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide) 0x15) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1250bf [0xC6, 0x43, 0x14, 0x01] (StorePre 0x1250bf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x1250bf + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1250bf (.base 3 (.d8 0x14)) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1250bf (.base 3 (.d8 0x14)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x1250bf (.base 3 (.d8 0x14)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250ad) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250b1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250b8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250bb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250bf) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250c3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 60) (jmp_rel8_effect_step 0x1250c3 0xc8 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1250a8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1250a8 :=
  Rest.liftedBlock (rest_l1250a8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1250a8 x hx)

theorem rest_l1250c5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1250c5 bytes_l1250c5) (entryMap (live .l1250c5))
      15 0x1250c5 bytes_l1250c5 b_l1250c5 := by
  have f0 : InstrSpec 0x1250c5 [0x8B, 0x4C, 0x24, 0x34] (LoadPre 0x1250c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x1250c5 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1250c5 1 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x1250c5 1 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r32_m32_low_effect_step 0x1250c5 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1250c9 [0x89, 0x4C, 0x24, 0x7C] (StorePre 0x1250c9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x1250c9 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1250c9 1 (.sib 4 none 0 (.d8 0x7c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1250c9 1 (.sib 4 none 0 (.d8 0x7c))).toInstrSpec (mov_m32_r32_low_effect_step 0x1250c9 1 (.sib 4 none 0 (.d8 0x7c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1250cd [0x48, 0x8B, 0x4C, 0x24, 0x2C] (LoadPre 0x1250cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x1250cd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1250cd 1 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1250cd 1 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x1250cd 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1250d2 [0x48, 0x89, 0x4C, 0x24, 0x74] (StorePre 0x1250d2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x1250d2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1250d2 1 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1250d2 1 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (mov_m64_r64_effect_step 0x1250d2 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1250d7 [0x48, 0x8B, 0x4C, 0x24, 0x24] (LoadPre 0x1250d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1250d7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1250d7 1 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1250d7 1 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x1250d7 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1250dc [0x48, 0x89, 0x4C, 0x24, 0x6C] (StorePre 0x1250dc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x1250dc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1250dc 1 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1250dc 1 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (mov_m64_r64_effect_step 0x1250dc 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1250e1 [0x48, 0x8B, 0x4C, 0x24, 0x14] (LoadPre 0x1250e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1250e1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1250e1 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1250e1 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x1250e1 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1250e6 [0x48, 0x8B, 0x54, 0x24, 0x1C] (LoadPre 0x1250e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1250e6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1250e6 2 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1250e6 2 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x1250e6 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1250eb [0x48, 0x89, 0x54, 0x24, 0x64] (StorePre 0x1250eb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x1250eb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1250eb 2 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1250eb 2 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (mov_m64_r64_effect_step 0x1250eb 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1250f0 [0x48, 0x89, 0x4C, 0x24, 0x5C] (StorePre 0x1250f0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x1250f0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1250f0 1 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1250f0 1 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (mov_m64_r64_effect_step 0x1250f0 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1250f5 [0x48, 0x8B, 0x4C, 0x24, 0x38] (LoadPre 0x1250f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1250f5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1250f5 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1250f5 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1250f5 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1250fa [0x48, 0x8B, 0x54, 0x24, 0x40] (LoadPre 0x1250fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1250fa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1250fa 2 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1250fa 2 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1250fa 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1250ff [0x48, 0x89, 0x4C, 0x24, 0x4C] (StorePre 0x1250ff 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x1250ff + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1250ff 1 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1250ff 1 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_m64_r64_effect_step 0x1250ff 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x125104 [0x48, 0x89, 0x54, 0x24, 0x54] (StorePre 0x125104 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x125104 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125104 2 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125104 2 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_m64_r64_effect_step 0x125104 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250c9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250cd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250d2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250d7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250dc) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250e1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 62), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250e6) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250eb) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250f0) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250f5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 68), (2, 64), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250fa) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1250ff) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125104) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125109) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 74) (jmp_rel8_effect_step 0x125109 0x44 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1250c5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1250c5 :=
  Rest.liftedBlock (rest_l1250c5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1250c5 x hx)

theorem rest_l12510b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12510b bytes_l12510b) (entryMap (live .l12510b))
      14 0x12510b bytes_l12510b b_l12510b := by
  have f0 : InstrSpec 0x12510b [0x48, 0x8B, 0x4C, 0x24, 0x04] (LoadPre 0x12510b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x12510b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12510b 1 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12510b 1 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r64_m64_effect_step 0x12510b 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125110 [0x48, 0x8B, 0x54, 0x24, 0x0C] (LoadPre 0x125110 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x125110 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125110 2 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125110 2 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r64_m64_effect_step 0x125110 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x125115 [0x48, 0x89, 0x54, 0x24, 0x54] (StorePre 0x125115 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x125115 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125115 2 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125115 2 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_m64_r64_effect_step 0x125115 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x12511a [0x48, 0x8B, 0x54, 0x24, 0x14] (LoadPre 0x12511a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x12511a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12511a 2 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12511a 2 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x12511a 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x12511f [0x48, 0x89, 0x54, 0x24, 0x5C] (StorePre 0x12511f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x12511f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12511f 2 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12511f 2 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (mov_m64_r64_effect_step 0x12511f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x125124 [0x48, 0x8B, 0x54, 0x24, 0x1C] (LoadPre 0x125124 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x125124 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125124 2 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125124 2 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x125124 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x125129 [0x48, 0x89, 0x54, 0x24, 0x64] (StorePre 0x125129 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x125129 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125129 2 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125129 2 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (mov_m64_r64_effect_step 0x125129 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x12512e [0x48, 0x8B, 0x54, 0x24, 0x24] (LoadPre 0x12512e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x12512e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12512e 2 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12512e 2 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x12512e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x125133 [0x48, 0x89, 0x54, 0x24, 0x6C] (StorePre 0x125133 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x125133 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125133 2 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125133 2 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (mov_m64_r64_effect_step 0x125133 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x125138 [0x48, 0x8B, 0x54, 0x24, 0x2C] (LoadPre 0x125138 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x125138 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125138 2 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125138 2 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x125138 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x12513d [0x48, 0x89, 0x54, 0x24, 0x74] (StorePre 0x12513d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x12513d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12513d 2 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12513d 2 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (mov_m64_r64_effect_step 0x12513d 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x125142 [0x8B, 0x54, 0x24, 0x34] (LoadPre 0x125142 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x125142 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125142 2 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x125142 2 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r32_m32_low_effect_step 0x125142 2 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x125146 [0x89, 0x54, 0x24, 0x7C] (StorePre 0x125146 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x125146 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x125146 2 (.sib 4 none 0 (.d8 0x7c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125146 2 (.sib 4 none 0 (.d8 0x7c))).toInstrSpec (mov_m32_r32_low_effect_step 0x125146 2 (.sib 4 none 0 (.d8 0x7c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x12514a [0x48, 0x89, 0x4C, 0x24, 0x4C] (StorePre 0x12514a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x12514a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12514a 1 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12514a 1 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_m64_r64_effect_step 0x12514a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125110) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125115) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12511a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 53), (2, 58), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12511f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 58), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125124) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (2, 61), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125129) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 61), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12512e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 53), (2, 64), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125133) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 64), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125138) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 53), (2, 67), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12513d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 53), (2, 67), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125142) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125146) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12514a) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12514f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 74) (by decide) rfl

theorem block_l12510b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12510b :=
  Rest.liftedBlock (rest_l12510b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12510b x hx)

theorem rest_l12514f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12514f bytes_l12514f) (entryMap (live .l12514f))
      16 0x12514f bytes_l12514f b_l12514f := by
  have f0 : InstrSpec 0x12514f [0x8B, 0x4C, 0x24, 0x4C] (LoadPre 0x12514f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x12514f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12514f 1 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x12514f 1 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_r32_m32_low_effect_step 0x12514f 1 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125153 [0x48, 0x8B, 0x54, 0x24, 0x50] (LoadPre 0x125153 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x125153 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125153 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125153 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x125153 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x125158 [0x48, 0x8B, 0x74, 0x24, 0x58] (LoadPre 0x125158 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x125158 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125158 6 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125158 6 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x125158 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12515d [0x48, 0x8B, 0x7C, 0x24, 0x78] (LoadPre 0x12515d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x12515d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12515d 7 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12515d 7 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x12515d 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x125162 [0x48, 0x89, 0x7B, 0x38] (StorePre 0x125162 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x125162 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125162 7 (.base 3 (.d8 0x38)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125162 7 (.base 3 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x125162 0x48 (by decide) 7 (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x125166 [0x48, 0x8B, 0x7C, 0x24, 0x70] (LoadPre 0x125166 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x125166 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125166 7 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x125166 7 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x125166 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x12516b [0x48, 0x89, 0x7B, 0x30] (StorePre 0x12516b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x12516b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12516b 7 (.base 3 (.d8 0x30)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12516b 7 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x12516b 0x48 (by decide) 7 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x12516f [0x48, 0x8B, 0x7C, 0x24, 0x68] (LoadPre 0x12516f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x12516f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12516f 7 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12516f 7 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x12516f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x125174 [0x48, 0x89, 0x7B, 0x28] (StorePre 0x125174 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x125174 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125174 7 (.base 3 (.d8 0x28)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125174 7 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x125174 0x48 (by decide) 7 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x125178 [0x48, 0x8B, 0x7C, 0x24, 0x60] (LoadPre 0x125178 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x125178 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125178 7 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x125178 7 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x125178 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x12517d [0x48, 0x89, 0x7B, 0x20] (StorePre 0x12517d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x12517d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12517d 7 (.base 3 (.d8 0x20)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12517d 7 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x12517d 0x48 (by decide) 7 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x125181 [0x89, 0x43, 0x08] (StorePre 0x125181 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x125181 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125181 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125181 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x125181 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x125184 [0x89, 0x4B, 0x0C] (StorePre 0x125184 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x125184 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125184 1 (.base 3 (.d8 0xc)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125184 1 (.base 3 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x125184 1 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x125187 [0x48, 0x89, 0x53, 0x10] (StorePre 0x125187 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x125187 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125187 2 (.base 3 (.d8 0x10)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125187 2 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x125187 0x48 (by decide) 2 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x12518b [0x48, 0x89, 0x73, 0x18] (StorePre 0x12518b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x12518b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12518b 6 (.base 3 (.d8 0x18)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12518b 6 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x12518b 0x48 (by decide) 6 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125153) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125158) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12515d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125162) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125166) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12516b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12516f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125174) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125178) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12517d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125181) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125184) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125187) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12518b) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12518f) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 75) (jmp_rel32_effect_step 0x12518f 0xfffffef9 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12514f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12514f :=
  Rest.liftedBlock (rest_l12514f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12514f x hx)

theorem rest_l125194_2 [Bindings] (code : CodeMap) :
    Rest (n := 115) code lifted (codeRange 0x125194 bytes_l125194) [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 113), (8, 97), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]
      10 0x12528a bytes_l125194_2 b_l125194_2 := by
  have f40 : InstrSpec 0x12528a [0x48, 0x89, 0x7B, 0x1D] (StorePre 0x12528a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1d)) s (0x12528a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12528a 7 (.base 3 (.d8 0x1d)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12528a 7 (.base 3 (.d8 0x1d))).toInstrSpec (mov_m64_r64_effect_step 0x12528a 0x48 (by decide) 7 (.base 3 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f41 : InstrSpec 0x12528e [0x48, 0x8B, 0xBC, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x12528e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x12528e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12528e 7 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12528e 7 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x12528e 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f42 : InstrSpec 0x125296 [0x4C, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x125296 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x125296 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125296 8 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x125296 8 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x125296 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f43 : InstrSpec 0x12529e [0x4C, 0x89, 0x43, 0x15] (StorePre 0x12529e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x12529e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12529e 8 (.base 3 (.d8 0x15)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12529e 8 (.base 3 (.d8 0x15))).toInstrSpec (mov_m64_r64_effect_step 0x12529e 0x4c (by decide) 0 (.base 3 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f44 : InstrSpec 0x1252a2 [0x48, 0x89, 0x7B, 0x0D] (StorePre 0x1252a2 4 (fun s => AddrMode.addr (.base 3 (.d8 0xd)) s (0x1252a2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1252a2 7 (.base 3 (.d8 0xd)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1252a2 7 (.base 3 (.d8 0xd))).toInstrSpec (mov_m64_r64_effect_step 0x1252a2 0x48 (by decide) 7 (.base 3 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x1252a6 [0x89, 0x43, 0x08] (StorePre 0x1252a6 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1252a6 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1252a6 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1252a6 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x1252a6 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f46 : InstrSpec 0x1252a9 [0x88, 0x4B, 0x0C] (StorePre 0x1252a9 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x1252a9 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1252a9 3 1 (.base 3 (.d8 0xc)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x1252a9 3 1 (.base 3 (.d8 0xc))).toInstrSpec (mov_m8_r8_effect_step 0x1252a9 1 (by decide) (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f47 : InstrSpec 0x1252ac [0x88, 0x53, 0x38] (StorePre 0x1252ac 3 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x1252ac + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1252ac 3 2 (.base 3 (.d8 0x38)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x1252ac 3 2 (.base 3 (.d8 0x38))).toInstrSpec (mov_m8_r8_effect_step 0x1252ac 2 (by decide) (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x1252af [0x89, 0x73, 0x3C] (StorePre 0x1252af 3 (fun s => AddrMode.addr (.base 3 (.d8 0x3c)) s (0x1252af + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1252af 6 (.base 3 (.d8 0x3c)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1252af 6 (.base 3 (.d8 0x3c))).toInstrSpec (mov_m32_r32_low_effect_step 0x1252af 6 (.base 3 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 115) (RestInside.exec (n := 115) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 113), (8, 97), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12528e) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f41 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 116), (8, 97), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125296) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f42 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 116), (8, 118), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12529e) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.exec (n := 120) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 116), (8, 118), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252a2) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 121) (RestInside.exec (n := 121) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 116), (8, 118), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252a6) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 122) (RestInside.exec (n := 122) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 116), (8, 118), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252a9) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 123) (RestInside.exec (n := 123) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 116), (8, 118), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252ac) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 124) (RestInside.exec (n := 124) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 116), (8, 118), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252af) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 125) (RestInside.exec (n := 125) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 116), (8, 118), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252b2) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 126) (jmp_rel32_effect_step 0x1252b2 0xfffffdd6 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l125194_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x125194 bytes_l125194) [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 81), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]
      30 0x125204 bytes_l125194_1 b_l125194_1 := by
  have f20 : InstrSpec 0x125204 [0x8B, 0x74, 0x24, 0x34] (LoadPre 0x125204 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x125204 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125204 6 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x125204 6 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r32_m32_low_effect_step 0x125204 6 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x125208 [0x48, 0x8B, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x125208 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x125208 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125208 7 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x125208 7 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x125208 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x125210 [0x48, 0x89, 0xBC, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x125210 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x125210 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125210 7 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125210 7 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x125210 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x125218 [0x48, 0x8B, 0xBC, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x125218 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x125218 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125218 7 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x125218 7 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x125218 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x125220 [0x48, 0x89, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x125220 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x125220 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125220 7 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125220 7 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x125220 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x125228 [0x48, 0x8B, 0xBC, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x125228 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x125228 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125228 7 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x125228 7 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x125228 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x125230 [0x48, 0x89, 0xBC, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x125230 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x125230 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125230 7 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125230 7 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x125230 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x125238 [0x48, 0x8B, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x125238 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x125238 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125238 7 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x125238 7 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x125238 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x125240 [0x4C, 0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x125240 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x125240 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125240 8 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x125240 8 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x125240 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x125248 [0x4C, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x125248 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x125248 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125248 8 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125248 8 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x125248 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x125250 [0x48, 0x89, 0xBC, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x125250 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x125250 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125250 7 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125250 7 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x125250 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x125258 [0x0F, 0xB6, 0x7C, 0x24, 0x3A] (LoadPre 0x125258 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x125258 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125258 5 7 (.sib 4 none 0 (.d8 0x3a)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x125258 5 7 (.sib 4 none 0 (.d8 0x3a))).toInstrSpec (movzx_r32_m8_effect_step 0x125258 7 (.sib 4 none 0 (.d8 0x3a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x12525d [0x40, 0x88, 0x7B, 0x37] (StorePre 0x12525d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x37)) s (0x12525d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x12525d 4 7 (.base 3 (.d8 0x37)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x12525d 4 7 (.base 3 (.d8 0x37))).toInstrSpec (mov_m8_r8_rex_effect_step 0x12525d 0x40 (by decide) 7 (.base 3 (.d8 0x37)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x125261 [0x0F, 0xB7, 0x7C, 0x24, 0x38] (LoadPre 0x125261 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x125261 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x125261 5 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M16Effect_footprint 0x125261 5 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (movzx_r32_m16_effect_step 0x125261 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f34 : InstrSpec 0x125266 [0x66, 0x89, 0x7B, 0x35] (StorePre 0x125266 4 (fun s => AddrMode.addr (.base 3 (.d8 0x35)) s (0x125266 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x125266 4 7 (.base 3 (.d8 0x35)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x125266 4 7 (.base 3 (.d8 0x35))).toInstrSpec (mov_m16_r16_effect_step 0x125266 7 (.base 3 (.d8 0x35)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x12526a [0x48, 0x8B, 0xBC, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x12526a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x12526a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12526a 7 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12526a 7 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x12526a 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x125272 [0x48, 0x89, 0x7B, 0x2D] (StorePre 0x125272 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2d)) s (0x125272 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125272 7 (.base 3 (.d8 0x2d)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125272 7 (.base 3 (.d8 0x2d))).toInstrSpec (mov_m64_r64_effect_step 0x125272 0x48 (by decide) 7 (.base 3 (.d8 0x2d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x125276 [0x48, 0x8B, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x125276 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x125276 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125276 7 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x125276 7 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x125276 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f38 : InstrSpec 0x12527e [0x48, 0x89, 0x7B, 0x25] (StorePre 0x12527e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x25)) s (0x12527e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12527e 7 (.base 3 (.d8 0x25)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12527e 7 (.base 3 (.d8 0x25))).toInstrSpec (mov_m64_r64_effect_step 0x12527e 0x48 (by decide) 7 (.base 3 (.d8 0x25)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x125282 [0x48, 0x8B, 0xBC, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x125282 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x125282 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125282 7 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x125282 7 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x125282 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125208) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f21 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 86), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125210) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 86), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125218) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f23 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 89), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125220) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 89), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125228) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f25 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 92), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125230) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 92), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125238) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f27 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 95), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125240) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f28 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 95), (8, 97), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125248) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 95), (8, 97), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125250) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 95), (8, 97), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125258) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f31 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 101), (8, 97), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12525d) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.exec (n := 103) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 101), (8, 97), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125261) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f33 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 104), (8, 97), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125266) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 104), (8, 97), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12526a) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f35 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 107), (8, 97), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125272) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.exec (n := 109) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 107), (8, 97), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125276) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f37 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 110), (8, 97), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12527e) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.exec (n := 112) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 110), (8, 97), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125282) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f39 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 113), (8, 97), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12528a) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l125194_2 code

theorem rest_l125194 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125194 bytes_l125194) (entryMap (live .l125194))
      50 0x125194 bytes_l125194 b_l125194 := by
  have f0 : InstrSpec 0x125194 [0x0F, 0xB6, 0x4C, 0x24, 0x04] (LoadPre 0x125194 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x125194 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125194 5 1 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x125194 5 1 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (movzx_r32_m8_effect_step 0x125194 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125199 [0x48, 0x8B, 0x54, 0x24, 0x05] (LoadPre 0x125199 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5)) s (0x125199 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125199 2 (.sib 4 none 0 (.d8 0x5)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125199 2 (.sib 4 none 0 (.d8 0x5))).toInstrSpec (mov_r64_m64_effect_step 0x125199 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12519e [0x48, 0x89, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x12519e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x12519e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12519e 2 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12519e 2 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x12519e 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1251a6 [0x48, 0x8B, 0x54, 0x24, 0x0D] (LoadPre 0x1251a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x1251a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1251a6 2 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1251a6 2 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (mov_r64_m64_effect_step 0x1251a6 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1251ab [0x48, 0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1251ab 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1251ab + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1251ab 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1251ab 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x1251ab 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1251b3 [0x48, 0x8B, 0x54, 0x24, 0x15] (LoadPre 0x1251b3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x1251b3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1251b3 2 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1251b3 2 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (mov_r64_m64_effect_step 0x1251b3 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1251b8 [0x48, 0x89, 0x94, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x1251b8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1251b8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1251b8 2 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1251b8 2 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x1251b8 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1251c0 [0x48, 0x8B, 0x54, 0x24, 0x1D] (LoadPre 0x1251c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x1251c0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1251c0 2 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1251c0 2 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (mov_r64_m64_effect_step 0x1251c0 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1251c5 [0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x1251c5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1251c5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1251c5 2 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1251c5 2 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x1251c5 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1251cd [0x48, 0x8B, 0x54, 0x24, 0x25] (LoadPre 0x1251cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x1251cd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1251cd 2 (.sib 4 none 0 (.d8 0x25)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1251cd 2 (.sib 4 none 0 (.d8 0x25))).toInstrSpec (mov_r64_m64_effect_step 0x1251cd 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1251d2 [0x48, 0x89, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x1251d2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1251d2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1251d2 2 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1251d2 2 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x1251d2 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1251da [0x0F, 0xB7, 0x54, 0x24, 0x2D] (LoadPre 0x1251da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x1251da + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1251da 5 2 (.sib 4 none 0 (.d8 0x2d)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x1251da 5 2 (.sib 4 none 0 (.d8 0x2d))).toInstrSpec (movzx_r32_m16_effect_step 0x1251da 2 (.sib 4 none 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1251df [0x66, 0x89, 0x54, 0x24, 0x38] (StorePre 0x1251df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1251df + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1251df 5 2 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1251df 5 2 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m16_r16_effect_step 0x1251df 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1251e4 [0x0F, 0xB6, 0x54, 0x24, 0x2F] (LoadPre 0x1251e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2f)) s (0x1251e4 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1251e4 5 2 (.sib 4 none 0 (.d8 0x2f)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1251e4 5 2 (.sib 4 none 0 (.d8 0x2f))).toInstrSpec (movzx_r32_m8_effect_step 0x1251e4 2 (.sib 4 none 0 (.d8 0x2f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1251e9 [0x88, 0x54, 0x24, 0x3A] (StorePre 0x1251e9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x1251e9 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1251e9 4 2 (.sib 4 none 0 (.d8 0x3a)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1251e9 4 2 (.sib 4 none 0 (.d8 0x3a))).toInstrSpec (mov_m8_r8_effect_step 0x1251e9 2 (by decide) (.sib 4 none 0 (.d8 0x3a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1251ed [0x0F, 0xB6, 0x54, 0x24, 0x30] (LoadPre 0x1251ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1251ed + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1251ed 5 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1251ed 5 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (movzx_r32_m8_effect_step 0x1251ed 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x1251f2 [0x0F, 0xB6, 0x74, 0x24, 0x33] (LoadPre 0x1251f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x33)) s (0x1251f2 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1251f2 5 6 (.sib 4 none 0 (.d8 0x33)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x1251f2 5 6 (.sib 4 none 0 (.d8 0x33))).toInstrSpec (movzx_r32_m8_effect_step 0x1251f2 6 (.sib 4 none 0 (.d8 0x33)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x1251f7 [0x40, 0x88, 0x73, 0x3B] (StorePre 0x1251f7 4 (fun s => AddrMode.addr (.base 3 (.d8 0x3b)) s (0x1251f7 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1251f7 4 6 (.base 3 (.d8 0x3b)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x1251f7 4 6 (.base 3 (.d8 0x3b))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1251f7 0x40 (by decide) 6 (.base 3 (.d8 0x3b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1251fb [0x0F, 0xB7, 0x74, 0x24, 0x31] (LoadPre 0x1251fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x1251fb + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1251fb 5 6 (.sib 4 none 0 (.d8 0x31)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M16Effect_footprint 0x1251fb 5 6 (.sib 4 none 0 (.d8 0x31))).toInstrSpec (movzx_r32_m16_effect_step 0x1251fb 6 (.sib 4 none 0 (.d8 0x31)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x125200 [0x66, 0x89, 0x73, 0x39] (StorePre 0x125200 4 (fun s => AddrMode.addr (.base 3 (.d8 0x39)) s (0x125200 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x125200 4 6 (.base 3 (.d8 0x39)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x125200 4 6 (.base 3 (.d8 0x39))).toInstrSpec (mov_m16_r16_effect_step 0x125200 6 (.base 3 (.d8 0x39)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125199) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12519e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1251a6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 53), (2, 58), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1251ab) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 58), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1251b3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (2, 61), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1251b8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 61), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1251c0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 53), (2, 64), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1251c5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 64), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1251cd) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 53), (2, 67), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1251d2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 53), (2, 67), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1251da) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1251df) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1251e4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 53), (2, 73), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1251e9) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 53), (2, 73), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1251ed) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1251f2) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 78), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1251f7) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 78), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1251fb) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 81), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125200) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 81), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125204) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l125194_1 code

theorem block_l125194 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125194 :=
  Rest.liftedBlock (rest_l125194 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125194 x hx)

theorem rest_l1252b7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1252b7 bytes_l1252b7) (entryMap (live .l1252b7))
      11 0x1252b7 bytes_l1252b7 b_l1252b7 := by
  have f0 : InstrSpec 0x1252b7 [0x48, 0x8B, 0x44, 0x24, 0x6B] (LoadPre 0x1252b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6b)) s (0x1252b7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1252b7 0 (.sib 4 none 0 (.d8 0x6b)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1252b7 0 (.sib 4 none 0 (.d8 0x6b))).toInstrSpec (mov_r64_m64_effect_step 0x1252b7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x6b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1252bc [0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x1252bc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1252bc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1252bc 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1252bc 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x1252bc 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1252c4 [0x48, 0x8B, 0x44, 0x24, 0x63] (LoadPre 0x1252c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x63)) s (0x1252c4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1252c4 0 (.sib 4 none 0 (.d8 0x63)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1252c4 0 (.sib 4 none 0 (.d8 0x63))).toInstrSpec (mov_r64_m64_effect_step 0x1252c4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x63)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1252c9 [0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x1252c9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1252c9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1252c9 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1252c9 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x1252c9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1252d1 [0x48, 0x8B, 0x44, 0x24, 0x5B] (LoadPre 0x1252d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5b)) s (0x1252d1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1252d1 0 (.sib 4 none 0 (.d8 0x5b)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1252d1 0 (.sib 4 none 0 (.d8 0x5b))).toInstrSpec (mov_r64_m64_effect_step 0x1252d1 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x5b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1252d6 [0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x1252d6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1252d6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1252d6 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1252d6 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x1252d6 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1252de [0x48, 0x8B, 0x44, 0x24, 0x4B] (LoadPre 0x1252de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x1252de + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1252de 0 (.sib 4 none 0 (.d8 0x4b)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1252de 0 (.sib 4 none 0 (.d8 0x4b))).toInstrSpec (mov_r64_m64_effect_step 0x1252de 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x4b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1252e3 [0x48, 0x8B, 0x4C, 0x24, 0x53] (LoadPre 0x1252e3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x1252e3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1252e3 1 (.sib 4 none 0 (.d8 0x53)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1252e3 1 (.sib 4 none 0 (.d8 0x53))).toInstrSpec (mov_r64_m64_effect_step 0x1252e3 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x53)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1252e8 [0x48, 0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x1252e8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1252e8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1252e8 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1252e8 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x1252e8 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1252f0 [0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x1252f0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1252f0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1252f0 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1252f0 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x1252f0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1252f8 [0x40, 0xB5, 0x01] (fun s => s.RIP = 0x1252f8) (movR8Imm8Effect 0x1252f8 3 5 0x1)
      [.gpr 5] [] [.reg 5, .rip] :=
    (movR8Imm8Effect_footprint 0x1252f8 3 5 0x1).toInstrSpec (mov_r8_imm8_rex_effect_step 0x1252f8 0x40 (by decide) 0xb5 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252bc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252c4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252c9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252d1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252d6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252de) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252e3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252e8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252f0) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252f8) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252fb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 70) (by decide) rfl

theorem block_l1252b7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1252b7 :=
  Rest.liftedBlock (rest_l1252b7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1252b7 x hx)

theorem rest_l1252fb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1252fb bytes_l1252fb) (entryMap (live .l1252fb))
      4 0x1252fb bytes_l1252fb b_l1252fb := by
  have f0 : InstrSpec 0x1252fb [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x1252fb) (movR64R64Effect 0x1252fb 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1252fb 7 4).toInstrSpec (mov_r64_r64_effect_step 0x1252fb 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1252fe [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x1252fe) (movR64R64Effect 0x1252fe 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1252fe 6 14).toInstrSpec (mov_r64_r64_effect_step 0x1252fe 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x125301 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125301) (movR32Imm32Effect 0x125301 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x125301 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x125301 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x125306 [0xE8, 0x45, 0x0A, 0x00, 0x00] (PushPre 0x125306 5) (callEffect (fun _ => 0x125d50) 0x12530b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x125306 0x125d50 0x12530b).toInstrSpec (call_rel32_effect_step 0x125306 0xa45 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1252fe) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125301) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125306) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1252fb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1252fb :=
  Rest.liftedBlock (rest_l1252fb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1252fb x hx)

theorem rest_l12530b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12530b bytes_l12530b) (entryMap (live .l12530b))
      3 0x12530b bytes_l12530b b_l12530b := by
  have f0 : InstrSpec 0x12530b [0x8B, 0x04, 0x24] (LoadPre 0x12530b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12530b + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x12530b 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x12530b 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x12530b 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12530e [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x12530e) (cmpR32Imm8Effect 0x12530e 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x12530e 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x12530e 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12530e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125311) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x125311 5 0x1a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12530b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12530b :=
  Rest.liftedBlock (rest_l12530b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12530b x hx)

theorem rest_l125313 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125313 bytes_l125313) (entryMap (live .l125313))
      3 0x125313 bytes_l125313 b_l125313 := by
  have f0 : InstrSpec 0x125313 [0x0F, 0xB6, 0x54, 0x24, 0x18] (LoadPre 0x125313 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125313 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125313 5 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x125313 5 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (movzx_r32_m8_effect_step 0x125313 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125318 [0x80, 0x7C, 0x24, 0x24, 0x02] (LoadPre 0x125318 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x125318 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x125318 5 (.sib 4 none 0 (.d8 0x24)) 0x2)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x125318 5 (.sib 4 none 0 (.d8 0x24)) 0x2).toInstrSpec (cmp_m8_imm8_effect_step 0x125318 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide) 0x2) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125318) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12531d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x12531d 4 0x94) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125313 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125313 :=
  Rest.liftedBlock (rest_l125313 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125313 x hx)

theorem rest_l125323 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125323 bytes_l125323) (entryMap (live .l125323))
      2 0x125323 bytes_l125323 b_l125323 := by
  have f0 : InstrSpec 0x125323 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x125323 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125323 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125323 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x125323 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x125323 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125328) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x125328 0x8c (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l125323 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125323 :=
  Rest.liftedBlock (rest_l125323 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125323 x hx)

theorem rest_l12532d_1 [Bindings] (code : CodeMap) :
    Rest (n := 87) code lifted (codeRange 0x12532d bytes_l12532d) [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 83), (11, 85), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]
      10 0x125390 bytes_l12532d_1 b_l12532d_1 := by
  have f20 : InstrSpec 0x125390 [0x44, 0x89, 0x5B, 0x24] (StorePre 0x125390 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x125390 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x125390 11 (.base 3 (.d8 0x24)))
      [.gpr 11, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x125390 11 (.base 3 (.d8 0x24))).toInstrSpec (mov_m32_r32_effect_step 0x125390 0x44 (by decide) 3 (.base 3 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x125394 [0x44, 0x89, 0x53, 0x21] (StorePre 0x125394 4 (fun s => AddrMode.addr (.base 3 (.d8 0x21)) s (0x125394 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x125394 10 (.base 3 (.d8 0x21)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x125394 10 (.base 3 (.d8 0x21))).toInstrSpec (mov_m32_r32_effect_step 0x125394 0x44 (by decide) 2 (.base 3 (.d8 0x21)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x125398 [0x89, 0x43, 0x08] (StorePre 0x125398 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x125398 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125398 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125398 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x125398 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x12539b [0x89, 0x4B, 0x0C] (StorePre 0x12539b 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x12539b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12539b 1 (.base 3 (.d8 0xc)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x12539b 1 (.base 3 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x12539b 1 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x12539e [0x48, 0x89, 0x53, 0x10] (StorePre 0x12539e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x12539e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12539e 2 (.base 3 (.d8 0x10)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12539e 2 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x12539e 0x48 (by decide) 2 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x1253a2 [0x48, 0x89, 0x73, 0x18] (StorePre 0x1253a2 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1253a2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1253a2 6 (.base 3 (.d8 0x18)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1253a2 6 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1253a2 0x48 (by decide) 6 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x1253a6 [0x40, 0x88, 0x7B, 0x20] (StorePre 0x1253a6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1253a6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1253a6 4 7 (.base 3 (.d8 0x20)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x1253a6 4 7 (.base 3 (.d8 0x20))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1253a6 0x40 (by decide) 7 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x1253aa [0x44, 0x89, 0x43, 0x28] (StorePre 0x1253aa 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1253aa + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1253aa 8 (.base 3 (.d8 0x28)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x1253aa 8 (.base 3 (.d8 0x28))).toInstrSpec (mov_m32_r32_effect_step 0x1253aa 0x44 (by decide) 0 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x1253ae [0x44, 0x88, 0x4B, 0x2C] (StorePre 0x1253ae 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x1253ae + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1253ae 4 9 (.base 3 (.d8 0x2c)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x1253ae 4 9 (.base 3 (.d8 0x2c))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1253ae 0x44 (by decide) 1 (.base 3 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 83), (11, 85), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125394) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 83), (11, 85), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125398) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 83), (11, 85), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12539b) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 83), (11, 85), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12539e) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 83), (11, 85), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253a2) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 83), (11, 85), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253a6) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 83), (11, 85), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253aa) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 83), (11, 85), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253ae) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 83), (11, 85), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253b2) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 96) (jmp_rel32_effect_step 0x1253b2 0xfffffcd6 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l12532d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12532d bytes_l12532d) (entryMap (live .l12532d))
      30 0x12532d bytes_l12532d b_l12532d := by
  have f0 : InstrSpec 0x12532d [0x8B, 0x4C, 0x24, 0x04] (LoadPre 0x12532d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x12532d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12532d 1 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x12532d 1 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_low_effect_step 0x12532d 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125331 [0x48, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x125331 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125331 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125331 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125331 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x125331 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x125336 [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x125336 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125336 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125336 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125336 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x125336 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12533b [0x0F, 0xB6, 0x7C, 0x24, 0x18] (LoadPre 0x12533b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12533b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x12533b 5 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x12533b 5 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (movzx_r32_m8_effect_step 0x12533b 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x125340 [0x44, 0x8B, 0x44, 0x24, 0x19] (LoadPre 0x125340 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x125340 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125340 8 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x125340 8 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (mov_r32_m32_effect_step 0x125340 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x125345 [0x44, 0x89, 0x44, 0x24, 0x48] (StorePre 0x125345 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x125345 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x125345 8 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x125345 8 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m32_r32_effect_step 0x125345 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x12534a [0x44, 0x8B, 0x44, 0x24, 0x1C] (LoadPre 0x12534a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x12534a + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x12534a 8 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x12534a 8 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x12534a 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x12534f [0x44, 0x89, 0x44, 0x24, 0x4B] (StorePre 0x12534f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x12534f + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x12534f 8 (.sib 4 none 0 (.d8 0x4b)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x12534f 8 (.sib 4 none 0 (.d8 0x4b))).toInstrSpec (mov_m32_r32_effect_step 0x12534f 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x4b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x125354 [0x44, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x125354 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x125354 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125354 8 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x125354 8 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r32_m32_effect_step 0x125354 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x125359 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x24] (LoadPre 0x125359 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x125359 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x125359 6 9 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x125359 6 9 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x125359 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x12535f [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x27] (LoadPre 0x12535f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x12535f + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x12535f 6 10 (.sib 4 none 0 (.d8 0x27)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x12535f 6 10 (.sib 4 none 0 (.d8 0x27))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x12535f 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x27)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x125365 [0x44, 0x88, 0x53, 0x2F] (StorePre 0x125365 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2f)) s (0x125365 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x125365 4 10 (.base 3 (.d8 0x2f)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x125365 4 10 (.base 3 (.d8 0x2f))).toInstrSpec (mov_m8_r8_rex_effect_step 0x125365 0x44 (by decide) 2 (.base 3 (.d8 0x2f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x125369 [0x44, 0x0F, 0xB7, 0x54, 0x24, 0x25] (LoadPre 0x125369 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x125369 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x125369 6 10 (.sib 4 none 0 (.d8 0x25)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x125369 6 10 (.sib 4 none 0 (.d8 0x25))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x125369 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x12536f [0x66, 0x44, 0x89, 0x53, 0x2D] (StorePre 0x12536f 5 (fun s => AddrMode.addr (.base 3 (.d8 0x2d)) s (0x12536f + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x12536f 5 10 (.base 3 (.d8 0x2d)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x12536f 5 10 (.base 3 (.d8 0x2d))).toInstrSpec (mov_m16_r16_rex_effect_step 0x12536f 0x44 (by decide) 2 (.base 3 (.d8 0x2d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x125374 [0x4C, 0x8B, 0x54, 0x24, 0x28] (LoadPre 0x125374 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x125374 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125374 10 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x125374 10 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x125374 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x125379 [0x4C, 0x8B, 0x5C, 0x24, 0x30] (LoadPre 0x125379 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x125379 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125379 11 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x125379 11 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x125379 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x12537e [0x4C, 0x89, 0x53, 0x30] (StorePre 0x12537e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x12537e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12537e 10 (.base 3 (.d8 0x30)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12537e 10 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x12537e 0x4c (by decide) 2 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x125382 [0x4C, 0x89, 0x5B, 0x38] (StorePre 0x125382 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x125382 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125382 11 (.base 3 (.d8 0x38)))
      [.gpr 11, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125382 11 (.base 3 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x125382 0x4c (by decide) 3 (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x125386 [0x44, 0x8B, 0x54, 0x24, 0x48] (LoadPre 0x125386 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x125386 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125386 10 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x125386 10 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r32_m32_effect_step 0x125386 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x12538b [0x44, 0x8B, 0x5C, 0x24, 0x4B] (LoadPre 0x12538b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x12538b + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x12538b 11 (.sib 4 none 0 (.d8 0x4b)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR32M32Effect_footprint 0x12538b 11 (.sib 4 none 0 (.d8 0x4b))).toInstrSpec (mov_r32_m32_effect_step 0x12538b 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x4b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125331) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125336) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12533b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125340) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 61), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125345) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 61), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12534a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 64), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12534f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 64), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125354) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125359) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12535f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 71), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125365) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 71), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125369) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 74), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12536f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 74), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125374) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 77), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125379) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 77), (11, 79), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12537e) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 77), (11, 79), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125382) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 77), (11, 79), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125386) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f18 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 83), (11, 79), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12538b) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f19 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 83), (11, 85), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125390) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12532d_1 code

theorem block_l12532d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12532d :=
  Rest.liftedBlock (rest_l12532d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12532d x hx)

theorem rest_l1253b7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1253b7 bytes_l1253b7) (entryMap (live .l1253b7))
      1 0x1253b7 bytes_l1253b7 b_l1253b7 := by
  have f0 : InstrSpec 0x1253b7 [0x31, 0xC0] (fun s => s.RIP = 0x1253b7) (xorR32R32Effect 0x1253b7 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1253b7 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x1253b7 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253b9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1253b7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1253b7 :=
  Rest.liftedBlock (rest_l1253b7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1253b7 x hx)

theorem rest_l1253b9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1253b9 bytes_l1253b9) (entryMap (live .l1253b9))
      5 0x1253b9 bytes_l1253b9 b_l1253b9 := by
  have f0 : InstrSpec 0x1253b9 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x1253b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1253b9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1253b9 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1253b9 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1253b9 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1253be [0x84, 0xD2] (fun s => s.RIP = 0x1253be) (testR8R8Effect 0x1253be 2 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1253be 2 2 2).toInstrSpec (test_r8_r8_effect_step 0x1253be 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1253c0 [0x0F, 0x94, 0xC2] (fun s => s.RIP = 0x1253c0) (atFlags (condHolds 4) (setccR8Effect 0x1253c0 3 2))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (setccR8Effect_footprint 0x1253c0 3 2 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1253c0 4 0xc2 (by decide) (by decide) c)) pre_rip
  have f3 : InstrSpec 0x1253c3 [0x48, 0x85, 0xC0] (fun s => s.RIP = 0x1253c3) (testR64R64Effect 0x1253c3 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1253c3 0 0).toInstrSpec (test_r64_r64_effect_step 0x1253c3 0x48 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253be) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253c0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253c3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253c6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x1253c6 4 0x2d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1253b9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1253b9 :=
  Rest.liftedBlock (rest_l1253b9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1253b9 x hx)

theorem rest_l1253c8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1253c8 bytes_l1253c8) (entryMap (live .l1253c8))
      2 0x1253c8 bytes_l1253c8 b_l1253c8 := by
  have f0 : InstrSpec 0x1253c8 [0x84, 0xD2] (fun s => s.RIP = 0x1253c8) (testR8R8Effect 0x1253c8 2 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1253c8 2 2 2).toInstrSpec (test_r8_r8_effect_step 0x1253c8 0xd2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253ca) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1253ca 5 0x29) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1253c8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1253c8 :=
  Rest.liftedBlock (rest_l1253c8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1253c8 x hx)

theorem rest_l1253cc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1253cc bytes_l1253cc) (entryMap (live .l1253cc))
      7 0x1253cc bytes_l1253cc b_l1253cc := by
  have f0 : InstrSpec 0x1253cc [0xC7, 0x43, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1253cc 7 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1253cc + BitVec.ofNat 64 7)) 4) (movM32Imm32Effect 0x1253cc 7 (.base 3 (.d8 0x8)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1253cc 7 (.base 3 (.d8 0x8)) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x1253cc (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1253d3 [0xC6, 0x43, 0x10, 0x15] (StorePre 0x1253d3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1253d3 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1253d3 (.base 3 (.d8 0x10)) 0x15)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1253d3 (.base 3 (.d8 0x10)) 0x15).toInstrSpec (mov_m8_imm8_effect_step 0x1253d3 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide) 0x15) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1253d7 [0xC6, 0x43, 0x17, 0x00] (StorePre 0x1253d7 4 (fun s => AddrMode.addr (.base 3 (.d8 0x17)) s (0x1253d7 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1253d7 (.base 3 (.d8 0x17)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1253d7 (.base 3 (.d8 0x17)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1253d7 (.base 3 (.d8 0x17)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1253db [0x66, 0xC7, 0x43, 0x15, 0x00, 0x00] (StorePre 0x1253db 6 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x1253db + BitVec.ofNat 64 6)) 2) (movM16Imm16Effect 0x1253db (.base 3 (.d8 0x15)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM16Imm16Effect_footprint 0x1253db (.base 3 (.d8 0x15)) 0x0).toInstrSpec (mov_m16_imm16_effect_step 0x1253db (.base 3 (.d8 0x15)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1253e1 [0xC7, 0x43, 0x11, 0x00, 0x00, 0x00, 0x02] (StorePre 0x1253e1 7 (fun s => AddrMode.addr (.base 3 (.d8 0x11)) s (0x1253e1 + BitVec.ofNat 64 7)) 4) (movM32Imm32Effect 0x1253e1 7 (.base 3 (.d8 0x11)) 0x2000000)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1253e1 7 (.base 3 (.d8 0x11)) 0x2000000).toInstrSpec (mov_m32_imm32_effect_step 0x1253e1 (.base 3 (.d8 0x11)) (by decide) (by decide) (by decide) 0x2000000) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1253e8 [0x48, 0xC7, 0x43, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1253e8 8 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1253e8 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1253e8 (.base 3 (.d8 0x18)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1253e8 (.base 3 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1253e8 0x48 (by decide) (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253d3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253d7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253db) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253e1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253e8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253f0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x1253f0 0xfffffc98 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1253cc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1253cc :=
  Rest.liftedBlock (rest_l1253cc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1253cc x hx)

theorem rest_l1253f5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1253f5 bytes_l1253f5) (entryMap (live .l1253f5))
      17 0x1253f5 bytes_l1253f5 b_l1253f5 := by
  have f0 : InstrSpec 0x1253f5 [0x48, 0x8B, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x1253f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1253f5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1253f5 2 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1253f5 2 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x1253f5 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1253fd [0x48, 0x89, 0x53, 0x49] (StorePre 0x1253fd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x49)) s (0x1253fd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1253fd 2 (.base 3 (.d8 0x49)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1253fd 2 (.base 3 (.d8 0x49))).toInstrSpec (mov_m64_r64_effect_step 0x1253fd 0x48 (by decide) 2 (.base 3 (.d8 0x49)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x125401 [0x48, 0x8B, 0x94, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x125401 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x125401 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125401 2 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125401 2 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x125401 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x125409 [0x48, 0x89, 0x53, 0x41] (StorePre 0x125409 4 (fun s => AddrMode.addr (.base 3 (.d8 0x41)) s (0x125409 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125409 2 (.base 3 (.d8 0x41)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125409 2 (.base 3 (.d8 0x41))).toInstrSpec (mov_m64_r64_effect_step 0x125409 0x48 (by decide) 2 (.base 3 (.d8 0x41)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12540d [0x48, 0x8B, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x12540d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x12540d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12540d 2 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12540d 2 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x12540d 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x125415 [0x48, 0x89, 0x53, 0x39] (StorePre 0x125415 4 (fun s => AddrMode.addr (.base 3 (.d8 0x39)) s (0x125415 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125415 2 (.base 3 (.d8 0x39)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125415 2 (.base 3 (.d8 0x39))).toInstrSpec (mov_m64_r64_effect_step 0x125415 0x48 (by decide) 2 (.base 3 (.d8 0x39)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x125419 [0x48, 0x8B, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x125419 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x125419 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125419 2 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125419 2 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x125419 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x125421 [0x48, 0x8B, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x125421 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x125421 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125421 6 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125421 6 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x125421 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x125429 [0x48, 0x89, 0x73, 0x31] (StorePre 0x125429 4 (fun s => AddrMode.addr (.base 3 (.d8 0x31)) s (0x125429 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125429 6 (.base 3 (.d8 0x31)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125429 6 (.base 3 (.d8 0x31))).toInstrSpec (mov_m64_r64_effect_step 0x125429 0x48 (by decide) 6 (.base 3 (.d8 0x31)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12542d [0x48, 0x89, 0x53, 0x29] (StorePre 0x12542d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x29)) s (0x12542d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12542d 2 (.base 3 (.d8 0x29)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12542d 2 (.base 3 (.d8 0x29))).toInstrSpec (mov_m64_r64_effect_step 0x12542d 0x48 (by decide) 2 (.base 3 (.d8 0x29)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x125431 [0x4C, 0x89, 0x7B, 0x08] (StorePre 0x125431 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x125431 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125431 15 (.base 3 (.d8 0x8)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125431 15 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x125431 0x4c (by decide) 7 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x125435 [0x4C, 0x89, 0x63, 0x10] (StorePre 0x125435 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x125435 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125435 12 (.base 3 (.d8 0x10)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125435 12 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x125435 0x4c (by decide) 4 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x125439 [0x48, 0x89, 0x43, 0x18] (StorePre 0x125439 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x125439 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125439 0 (.base 3 (.d8 0x18)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125439 0 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x125439 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x12543d [0x48, 0x89, 0x4B, 0x20] (StorePre 0x12543d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x12543d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12543d 1 (.base 3 (.d8 0x20)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12543d 1 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x12543d 0x48 (by decide) 1 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x125441 [0x40, 0x88, 0x6B, 0x28] (StorePre 0x125441 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x125441 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x125441 4 5 (.base 3 (.d8 0x28)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x125441 4 5 (.base 3 (.d8 0x28))).toInstrSpec (mov_m8_r8_rex_effect_step 0x125441 0x40 (by decide) 5 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x125445 [0x31, 0xC0] (fun s => s.RIP = 0x125445) (xorR32R32Effect 0x125445 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x125445 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x125445 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1253fd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125401) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125409) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12540d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125415) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125419) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125421) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125429) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12542d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125431) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125435) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125439) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12543d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125441) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125445) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125447) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 75) (jmp_rel32_effect_step 0x125447 0xfffffc46 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1253f5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1253f5 :=
  Rest.liftedBlock (rest_l1253f5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1253f5 x hx)

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

theorem_by block_l124de0_eval :
    program.runBlock (dialect code) ⟨.l124de0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124dfd_eval :
    program.runBlock (dialect code) ⟨.l124dfd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124e1d_eval :
    program.runBlock (dialect code) ⟨.l124e1d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124e44_eval :
    program.runBlock (dialect code) ⟨.l124e44, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124e50_eval :
    program.runBlock (dialect code) ⟨.l124e50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124e65_eval :
    program.runBlock (dialect code) ⟨.l124e65, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124e72_eval :
    program.runBlock (dialect code) ⟨.l124e72, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124e7d_eval :
    program.runBlock (dialect code) ⟨.l124e7d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124e88_eval :
    program.runBlock (dialect code) ⟨.l124e88, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124ea8_eval :
    program.runBlock (dialect code) ⟨.l124ea8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124ecf_eval :
    program.runBlock (dialect code) ⟨.l124ecf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124edb_eval :
    program.runBlock (dialect code) ⟨.l124edb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124ef0_eval :
    program.runBlock (dialect code) ⟨.l124ef0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124efd_eval :
    program.runBlock (dialect code) ⟨.l124efd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124f14_eval :
    program.runBlock (dialect code) ⟨.l124f14, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124f20_eval :
    program.runBlock (dialect code) ⟨.l124f20, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124fb4_eval :
    program.runBlock (dialect code) ⟨.l124fb4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124fbb_eval :
    program.runBlock (dialect code) ⟨.l124fbb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125001_eval :
    program.runBlock (dialect code) ⟨.l125001, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125045_eval :
    program.runBlock (dialect code) ⟨.l125045, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12508d_eval :
    program.runBlock (dialect code) ⟨.l12508d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125092_eval :
    program.runBlock (dialect code) ⟨.l125092, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1250a8_eval :
    program.runBlock (dialect code) ⟨.l1250a8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1250c5_eval :
    program.runBlock (dialect code) ⟨.l1250c5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12510b_eval :
    program.runBlock (dialect code) ⟨.l12510b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12514f_eval :
    program.runBlock (dialect code) ⟨.l12514f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125194_eval :
    program.runBlock (dialect code) ⟨.l125194, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1252b7_eval :
    program.runBlock (dialect code) ⟨.l1252b7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1252fb_eval :
    program.runBlock (dialect code) ⟨.l1252fb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12530b_eval :
    program.runBlock (dialect code) ⟨.l12530b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125313_eval :
    program.runBlock (dialect code) ⟨.l125313, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125323_eval :
    program.runBlock (dialect code) ⟨.l125323, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12532d_eval :
    program.runBlock (dialect code) ⟨.l12532d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1253b7_eval :
    program.runBlock (dialect code) ⟨.l1253b7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1253b9_eval :
    program.runBlock (dialect code) ⟨.l1253b9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1253c8_eval :
    program.runBlock (dialect code) ⟨.l1253c8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1253cc_eval :
    program.runBlock (dialect code) ⟨.l1253cc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1253f5_eval :
    program.runBlock (dialect code) ⟨.l1253f5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
