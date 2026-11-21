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

theorem rest_l1002f0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1002f0 bytes_l1002f0) (entryMap (live .l1002f0))
      12 0x1002f0 bytes_l1002f0 b_l1002f0 := by
  have f0 : InstrSpec 0x1002f0 [0x55] (PushPre 0x1002f0 1) (pushR64Effect 0x1002f0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1002f0 1 5).toInstrSpec (push_r64_effect_step 0x1002f0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1002f1 [0x41, 0x57] (PushPre 0x1002f1 2) (pushR64Effect 0x1002f1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1002f1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1002f1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1002f3 [0x41, 0x56] (PushPre 0x1002f3 2) (pushR64Effect 0x1002f3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1002f3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1002f3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1002f5 [0x41, 0x54] (PushPre 0x1002f5 2) (pushR64Effect 0x1002f5 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1002f5 2 12).toInstrSpec (push_r64_rex_effect_step 0x1002f5 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1002f7 [0x53] (PushPre 0x1002f7 1) (pushR64Effect 0x1002f7 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1002f7 1 3).toInstrSpec (push_r64_effect_step 0x1002f7 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1002f8 [0x48, 0x83, 0xEC, 0x70] (fun s => s.RIP = 0x1002f8) (subR64Imm8Effect 0x1002f8 4 0x70)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1002f8 4 0x70).toInstrSpec (sub_r64_imm8_effect_step 0x1002f8 0x48 0xec 0x70 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1002fc [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x1002fc) (movR64R64Effect 0x1002fc 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1002fc 14 6).toInstrSpec (mov_r64_r64_effect_step 0x1002fc 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1002ff [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x1002ff) (movR64R64Effect 0x1002ff 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1002ff 3 7).toInstrSpec (mov_r64_r64_effect_step 0x1002ff 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100302 [0x8B, 0x6A, 0x08] (LoadPre 0x100302 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x100302 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100302 5 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR32M32LowEffect_footprint 0x100302 5 (.base 2 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x100302 5 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x100305 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x100305) (leaR64Effect 0x100305 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x100305 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x100305 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10030a [0x89, 0xEA] (fun s => s.RIP = 0x10030a) (movR32R32Effect 0x10030a 2 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x10030a 2 2 5).toInstrSpec (mov_r32_r32_effect_step 0x10030a 0xea (by decide)) pre_rip
  have f11 : InstrSpec 0x10030c [0xE8, 0x6F, 0x78, 0x02, 0x00] (PushPre 0x10030c 5) (callEffect (fun _ => 0x127b80) 0x100311)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10030c 0x127b80 0x100311).toInstrSpec (call_rel32_effect_step 0x10030c 0x2786f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002f1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002f3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002f5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002f7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002f8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002fc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002ff) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100302) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 2), (3, 67), (4, 63), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100305) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(2, 2), (3, 67), (4, 63), (5, 69), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10030a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(2, 73), (3, 67), (4, 63), (5, 69), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10030c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(2, 73), (3, 67), (4, 75), (5, 69), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l1002f0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1002f0 :=
  Rest.liftedBlock (rest_l1002f0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1002f0 x hx)

theorem rest_l100311 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100311 bytes_l100311) (entryMap (live .l100311))
      3 0x100311 bytes_l100311 b_l100311 := by
  have f0 : InstrSpec 0x100311 [0x8B, 0x44, 0x24, 0x08] (LoadPre 0x100311 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100311 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100311 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100311 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x100311 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100315 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x100315) (cmpR32Imm8Effect 0x100315 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x100315 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x100315 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100315) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100318) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x100318 5 0x1b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100311 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100311 :=
  Rest.liftedBlock (rest_l100311 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100311 x hx)

theorem rest_l10031a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10031a bytes_l10031a) (entryMap (live .l10031a))
      4 0x10031a bytes_l10031a b_l10031a := by
  have f0 : InstrSpec 0x10031a [0x4C, 0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x10031a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10031a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10031a 15 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10031a 15 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10031a 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10031f [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x10031f) (movR64R64Effect 0x10031f 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10031f 0 15).toInstrSpec (mov_r64_r64_effect_step 0x10031f 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100322 [0x48, 0xC1, 0xE8, 0x20] (fun s => s.RIP = 0x100322) (shrR64Effect 0x100322 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x100322 4 0 32).toInstrSpec (shr_r64_imm8_effect_step 0x100322 0x48 0xe8 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10031f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100322) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 58) f2 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x100322 4 0 32 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 53), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100326) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel32_effect_step 0x100326 4 0x80) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10031a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10031a :=
  Rest.liftedBlock (rest_l10031a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10031a x hx)

theorem rest_l10032c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10032c bytes_l10032c) (entryMap (live .l10032c))
      3 0x10032c bytes_l10032c b_l10032c := by
  have f0 : InstrSpec 0x10032c [0x31, 0xC0] (fun s => s.RIP = 0x10032c) (xorR32R32Effect 0x10032c 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10032c 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x10032c 0xc0 (by decide)) pre_rip
  have f1 : InstrSpec 0x10032e [0xB9, 0x0C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10032e) (movR32Imm32Effect 0x10032e 5 1 0xc)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10032e 5 1 0xc).toInstrSpec (mov_r32_imm32_effect_step 0x10032e 0xb9 (by decide) 0xc) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10032e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100333) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x100333 0x36 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10032c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10032c :=
  Rest.liftedBlock (rest_l10032c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10032c x hx)

theorem rest_l100335 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100335 bytes_l100335) (entryMap (live .l100335))
      11 0x100335 bytes_l100335 b_l100335 := by
  have f0 : InstrSpec 0x100335 [0x8B, 0x54, 0x24, 0x0C] (LoadPre 0x100335 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100335 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100335 2 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x100335 2 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x100335 2 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100339 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x100339 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100339 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100339 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100339 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x100339 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10033e [0x4C, 0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x10033e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10033e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10033e 15 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10033e 15 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10033e 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x100343 [0x48, 0x8B, 0x74, 0x24, 0x20] (LoadPre 0x100343 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100343 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100343 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x100343 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x100343 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x100348 [0x48, 0x89, 0x74, 0x24, 0x40] (StorePre 0x100348 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100348 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100348 6 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100348 6 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x100348 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10034d [0x48, 0x8B, 0x74, 0x24, 0x28] (LoadPre 0x10034d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10034d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10034d 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10034d 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10034d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x100352 [0x48, 0x89, 0x74, 0x24, 0x48] (StorePre 0x100352 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x100352 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100352 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100352 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x100352 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x100357 [0x48, 0x8B, 0x74, 0x24, 0x30] (LoadPre 0x100357 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100357 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100357 6 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x100357 6 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x100357 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10035c [0x48, 0x89, 0x74, 0x24, 0x50] (StorePre 0x10035c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10035c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10035c 6 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10035c 6 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x10035c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x100361 [0x48, 0x8B, 0x74, 0x24, 0x38] (LoadPre 0x100361 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x100361 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100361 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x100361 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x100361 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x100366 [0x48, 0x89, 0x74, 0x24, 0x58] (StorePre 0x100366 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100366 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100366 6 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100366 6 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x100366 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100339) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10033e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100343) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100348) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10034d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100352) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100357) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (6, 65), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10035c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (6, 65), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100361) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100366) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10036b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 71) (by decide) rfl

theorem block_l100335 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100335 :=
  Rest.liftedBlock (rest_l100335 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100335 x hx)

theorem rest_l10036b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10036b bytes_l10036b) (entryMap (live .l10036b))
      12 0x10036b bytes_l10036b b_l10036b := by
  have f0 : InstrSpec 0x10036b [0x89, 0x03] (StorePre 0x10036b 2 (fun s => AddrMode.addr (.base 3 .none) s (0x10036b + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x10036b 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10036b 0 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x10036b 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10036d [0x89, 0x53, 0x04] (StorePre 0x10036d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x10036d + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x10036d 2 (.base 3 (.d8 0x4)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10036d 2 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x10036d 2 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x100370 [0x48, 0x89, 0x4B, 0x08] (StorePre 0x100370 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x100370 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100370 1 (.base 3 (.d8 0x8)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x100370 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x100370 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x100374 [0x4C, 0x89, 0x7B, 0x10] (StorePre 0x100374 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x100374 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100374 15 (.base 3 (.d8 0x10)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x100374 15 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x100374 0x4c (by decide) 7 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x100378 [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x100378 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100378 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100378 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100378 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x100378 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10037d [0x48, 0x8B, 0x4C, 0x24, 0x48] (LoadPre 0x10037d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10037d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10037d 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10037d 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10037d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x100382 [0x48, 0x89, 0x43, 0x18] (StorePre 0x100382 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x100382 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100382 0 (.base 3 (.d8 0x18)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x100382 0 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x100382 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x100386 [0x48, 0x89, 0x4B, 0x20] (StorePre 0x100386 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x100386 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100386 1 (.base 3 (.d8 0x20)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x100386 1 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x100386 0x48 (by decide) 1 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10038a [0x48, 0x8B, 0x44, 0x24, 0x50] (LoadPre 0x10038a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10038a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10038a 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10038a 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x10038a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10038f [0x48, 0x89, 0x43, 0x28] (StorePre 0x10038f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x10038f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10038f 0 (.base 3 (.d8 0x28)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10038f 0 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10038f 0x48 (by decide) 0 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x100393 [0x48, 0x8B, 0x44, 0x24, 0x58] (LoadPre 0x100393 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100393 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100393 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100393 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x100393 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x100398 [0x48, 0x89, 0x43, 0x30] (StorePre 0x100398 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x100398 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100398 0 (.base 3 (.d8 0x30)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x100398 0 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x100398 0x48 (by decide) 0 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10036d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100370) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100374) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100378) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10037d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100382) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100386) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10038a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10038f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100393) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100398) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10039c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 69) (by decide) rfl

theorem block_l10036b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10036b :=
  Rest.liftedBlock (rest_l10036b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10036b x hx)

theorem rest_l10039c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10039c bytes_l10039c) (entryMap (live .l10039c))
      8 0x10039c bytes_l10039c b_l10039c := by
  have f0 : InstrSpec 0x10039c [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10039c) (movR64R64Effect 0x10039c 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10039c 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10039c 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10039f [0x48, 0x83, 0xC4, 0x70] (fun s => s.RIP = 0x10039f) (addR64Imm8Effect 0x10039f 4 0x70)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10039f 4 0x70).toInstrSpec (add_r64_imm8_effect_step 0x10039f 0x48 0xc4 0x70 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1003a3 [0x5B] (PopPre 0x1003a3) (popR64Effect 0x1003a3 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1003a3 1 3).toInstrSpec (pop_r64_effect_step 0x1003a3 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1003a4 [0x41, 0x5C] (PopPre 0x1003a4) (popR64Effect 0x1003a4 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1003a4 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1003a4 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1003a6 [0x41, 0x5E] (PopPre 0x1003a6) (popR64Effect 0x1003a6 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1003a6 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1003a6 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1003a8 [0x41, 0x5F] (PopPre 0x1003a8) (popR64Effect 0x1003a8 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1003a8 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1003a8 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1003aa [0x5D] (PopPre 0x1003aa) (popR64Effect 0x1003aa 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1003aa 1 5).toInstrSpec (pop_r64_effect_step 0x1003aa 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1003ab [0xC3] (RetPre 0x1003ab) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1003ab).toInstrSpec (ret_effect_step 0x1003ab) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10039f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003a3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003a4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003a6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003a8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 63), (15, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003aa) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 63), (15, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003ab) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 63), (15, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l10039c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10039c :=
  Rest.liftedBlock (rest_l10039c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10039c x hx)

theorem rest_l1003ac [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1003ac bytes_l1003ac) (entryMap (live .l1003ac))
      3 0x1003ac bytes_l1003ac b_l1003ac := by
  have f0 : InstrSpec 0x1003ac [0x48, 0xB8, 0x07, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1003ac) (movR64Imm64Effect 0x1003ac 0 0x100000007)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x1003ac 0 0x100000007).toInstrSpec (mov_r64_imm64_effect_step 0x1003ac 0x48 0xb8 (by decide) (by decide) 0x100000007) pre_rip
  have f1 : InstrSpec 0x1003b6 [0x4D, 0x85, 0xFF] (fun s => s.RIP = 0x1003b6) (testR64R64Effect 0x1003b6 15 15)
      [.gpr 15, .gpr 15] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1003b6 15 15).toInstrSpec (test_r64_r64_effect_step 0x1003b6 0x4d 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003b6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003b9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1003b9 4 0xc5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1003ac [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1003ac :=
  Rest.liftedBlock (rest_l1003ac code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1003ac x hx)

theorem rest_l1003bf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1003bf bytes_l1003bf) (entryMap (live .l1003bf))
      3 0x1003bf bytes_l1003bf b_l1003bf := by
  have f0 : InstrSpec 0x1003bf [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x1003bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1003bf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1003bf 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1003bf 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1003bf 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1003c4 [0x41, 0x83, 0xFF, 0x01] (fun s => s.RIP = 0x1003c4) (cmpR32Imm8Effect 0x1003c4 4 15 0x1)
      [.gpr 15] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1003c4 4 15 0x1).toInstrSpec (cmp_r32_imm8_rex_effect_step 0x1003c4 0x41 0xff 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003c4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003c8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1003c8 5 0xf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1003bf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1003bf :=
  Rest.liftedBlock (rest_l1003bf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1003bf x hx)

theorem rest_l1003ca [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1003ca bytes_l1003ca) (entryMap (live .l1003ca))
      3 0x1003ca bytes_l1003ca b_l1003ca := by
  have f0 : InstrSpec 0x1003ca [0x0F, 0xB6, 0x11] (LoadPre 0x1003ca (fun s => AddrMode.addr (.base 1 .none) s (0x1003ca + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x1003ca 3 2 (.base 1 .none))
      [.gpr 1] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1003ca 3 2 (.base 1 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x1003ca 2 (.base 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1003cd [0x84, 0xD2] (fun s => s.RIP = 0x1003cd) (testR8R8Effect 0x1003cd 2 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1003cd 2 2 2).toInstrSpec (test_r8_r8_effect_step 0x1003cd 0xd2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003cd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003cf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1003cf 5 0x13) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1003ca [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1003ca :=
  Rest.liftedBlock (rest_l1003ca code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1003ca x hx)

theorem rest_l1003d1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1003d1 bytes_l1003d1) (entryMap (live .l1003d1))
      2 0x1003d1 bytes_l1003d1 b_l1003d1 := by
  have f0 : InstrSpec 0x1003d1 [0x41, 0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1003d1) (movR32Imm32Effect 0x1003d1 6 15 0x1)
      [] [] [.reg 15, .rip] :=
    (movR32Imm32Effect_footprint 0x1003d1 6 15 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1003d1 0x41 0xbf (by decide) (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003d7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x1003d7 0x13 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1003d1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1003d1 :=
  Rest.liftedBlock (rest_l1003d1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1003d1 x hx)

theorem rest_l1003d9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1003d9 bytes_l1003d9) (entryMap (live .l1003d9))
      3 0x1003d9 bytes_l1003d9 b_l1003d9 := by
  have f0 : InstrSpec 0x1003d9 [0x0F, 0xB6, 0x11] (LoadPre 0x1003d9 (fun s => AddrMode.addr (.base 1 .none) s (0x1003d9 + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x1003d9 3 2 (.base 1 .none))
      [.gpr 1] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1003d9 3 2 (.base 1 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x1003d9 2 (.base 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1003dc [0x84, 0xD2] (fun s => s.RIP = 0x1003dc) (testR8R8Effect 0x1003dc 2 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1003dc 2 2 2).toInstrSpec (test_r8_r8_effect_step 0x1003dc 0xd2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003dc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003de) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1003de 4 0x9a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1003d9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1003d9 :=
  Rest.liftedBlock (rest_l1003d9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1003d9 x hx)

theorem rest_l1003e4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1003e4 bytes_l1003e4) (entryMap (live .l1003e4))
      2 0x1003e4 bytes_l1003e4 b_l1003e4 := by
  have f0 : InstrSpec 0x1003e4 [0x84, 0xD2] (fun s => s.RIP = 0x1003e4) (testR8R8Effect 0x1003e4 2 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1003e4 2 2 2).toInstrSpec (test_r8_r8_effect_step 0x1003e4 0xd2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (20, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003e6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1003e6 8 0x8c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1003e4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1003e4 :=
  Rest.liftedBlock (rest_l1003e4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1003e4 x hx)

theorem rest_l1003ec [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1003ec bytes_l1003ec) (entryMap (live .l1003ec))
      3 0x1003ec bytes_l1003ec b_l1003ec := by
  have f0 : InstrSpec 0x1003ec [0x48, 0xFF, 0xC9] (fun s => s.RIP = 0x1003ec) (decR64Effect 0x1003ec 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (decR64Effect_footprint 0x1003ec 1).toInstrSpec (dec_r64_effect_step 0x1003ec 0x48 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1003ef [0x49, 0xFF, 0xC7] (fun s => s.RIP = 0x1003ef) (incR64Effect 0x1003ef 15)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (incR64Effect_footprint 0x1003ef 15).toInstrSpec (inc_r64_effect_step 0x1003ef 0x49 0xc7 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1003f2 [0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1003f2) (fun _ => nopEffect 0x1003f2 14)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1003f2 14).toInstrSpec (nop_m_effect_step 0x1003f2 [0x66, 0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003ef) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003f2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100400) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l1003ec [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1003ec :=
  Rest.liftedBlock (rest_l1003ec code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1003ec x hx)

theorem rest_l100400 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100400 bytes_l100400) (entryMap (live .l100400))
      4 0x100400 bytes_l100400 b_l100400 := by
  have f0 : InstrSpec 0x100400 [0x4C, 0x8D, 0x61, 0x01] (fun s => s.RIP = 0x100400) (leaR64Effect 0x100400 12 (.base 1 (.d8 0x1)))
      [.gpr 1] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x100400 12 (.base 1 (.d8 0x1))).toInstrSpec (lea_r64_effect_step 0x100400 0x4c (by decide) 4 (.base 1 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100404 [0x49, 0x83, 0xFF, 0x02] (fun s => s.RIP = 0x100404) (cmpR64Imm8Effect 0x100404 15 0x2)
      [.gpr 15] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100404 15 0x2).toInstrSpec (cmp_r64_imm8_effect_step 0x100404 0x49 0xff 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100408 [0x4D, 0x8D, 0x7F, 0xFF] (fun s => s.RIP = 0x100408) (leaR64Effect 0x100408 15 (.base 15 (.d8 0xff)))
      [.gpr 15] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x100408 15 (.base 15 (.d8 0xff))).toInstrSpec (lea_r64_effect_step 0x100408 0x4d (by decide) 7 (.base 15 (.d8 0xff)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100404) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100408) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 57), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10040c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x10040c 4 0x9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100400 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100400 :=
  Rest.liftedBlock (rest_l100400 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100400 x hx)

theorem rest_l10040e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10040e bytes_l10040e) (entryMap (live .l10040e))
      3 0x10040e bytes_l10040e b_l10040e := by
  have f0 : InstrSpec 0x10040e [0x80, 0x79, 0x01, 0x00] (LoadPre 0x10040e (fun s => AddrMode.addr (.base 1 (.d8 0x1)) s (0x10040e + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x10040e 4 (.base 1 (.d8 0x1)) 0x0)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x10040e 4 (.base 1 (.d8 0x1)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x10040e (.base 1 (.d8 0x1)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100412 [0x4C, 0x89, 0xE1] (fun s => s.RIP = 0x100412) (movR64R64Effect 0x100412 1 12)
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x100412 1 12).toInstrSpec (mov_r64_r64_effect_step 0x100412 0x4c 0xe1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100412) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100415) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x100415 4 0xe9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10040e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10040e :=
  Rest.liftedBlock (rest_l10040e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10040e x hx)

theorem rest_l100417 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100417 bytes_l100417) (entryMap (live .l100417))
      3 0x100417 bytes_l100417 b_l100417 := by
  have f0 : InstrSpec 0x100417 [0x4C, 0x89, 0xF9] (fun s => s.RIP = 0x100417) (movR64R64Effect 0x100417 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x100417 1 15).toInstrSpec (mov_r64_r64_effect_step 0x100417 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10041a [0x48, 0xC1, 0xE9, 0x20] (fun s => s.RIP = 0x10041a) (shrR64Effect 0x10041a 4 1 32)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10041a 4 1 32).toInstrSpec (shr_r64_imm8_effect_step 0x10041a 0x48 0xe9 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10041a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 56) f1 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x10041a 4 1 32 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10041e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x10041e 4 0x1b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100417 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100417 :=
  Rest.liftedBlock (rest_l100417 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100417 x hx)

theorem rest_l100420 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100420 bytes_l100420) (entryMap (live .l100420))
      5 0x100420 bytes_l100420 b_l100420 := by
  have f0 : InstrSpec 0x100420 [0xC7, 0x03, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100420 6 (fun s => AddrMode.addr (.base 3 .none) s (0x100420 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x100420 6 (.base 3 .none) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x100420 6 (.base 3 .none) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x100420 (.base 3 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x100426 [0x48, 0x83, 0xC0, 0xFE] (fun s => s.RIP = 0x100426) (addR64Imm8Effect 0x100426 0 0xfe)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x100426 0 0xfe).toInstrSpec (add_r64_imm8_effect_step 0x100426 0x48 0xc0 0xfe (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10042a [0x48, 0x89, 0x43, 0x08] (StorePre 0x10042a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10042a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10042a 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10042a 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10042a 0x48 (by decide) 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10042e [0x48, 0xC7, 0x43, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10042e 8 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10042e + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10042e (.base 3 (.d8 0x10)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10042e (.base 3 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10042e 0x48 (by decide) (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100426) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10042a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10042e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100436) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 58) (jmp_rel32_effect_step 0x100436 0xffffff61 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100420 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100420 :=
  Rest.liftedBlock (rest_l100420 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100420 x hx)

theorem rest_l10043b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10043b bytes_l10043b) (entryMap (live .l10043b))
      5 0x10043b bytes_l10043b b_l10043b := by
  have f0 : InstrSpec 0x10043b [0x4C, 0x89, 0x64, 0x24, 0x60] (StorePre 0x10043b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10043b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10043b 12 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10043b 12 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x10043b 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x100440 [0x4C, 0x89, 0x7C, 0x24, 0x68] (StorePre 0x100440 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x100440 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100440 15 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100440 15 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x100440 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x100445 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x100445) (leaR64Effect 0x100445 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x100445 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x100445 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10044a [0x48, 0x8D, 0x74, 0x24, 0x60] (fun s => s.RIP = 0x10044a) (leaR64Effect 0x10044a 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10044a 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (lea_r64_effect_step 0x10044a 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10044f [0xE8, 0x9C, 0x71, 0x02, 0x00] (PushPre 0x10044f 5) (callEffect (fun _ => 0x1275f0) 0x100454)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10044f 0x1275f0 0x100454).toInstrSpec (call_rel32_effect_step 0x10044f 0x2719c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100440) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100445) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10044a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10044f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275f0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10043b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10043b :=
  Rest.liftedBlock (rest_l10043b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10043b x hx)

theorem rest_l100454 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100454 bytes_l100454) (entryMap (live .l100454))
      4 0x100454 bytes_l100454 b_l100454 := by
  have f0 : InstrSpec 0x100454 [0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x100454 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100454 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100454 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x100454 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x100454 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100458 [0x8B, 0x44, 0x24, 0x0C] (LoadPre 0x100458 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100458 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100458 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100458 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x100458 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10045c [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x10045c) (cmpR32Imm8Effect 0x10045c 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x10045c 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x10045c 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100458) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10045c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10045f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x10045f 5 0x3e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100454 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100454 :=
  Rest.liftedBlock (rest_l100454 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100454 x hx)

theorem rest_l100461 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100461 bytes_l100461) (entryMap (live .l100461))
      2 0x100461 bytes_l100461 b_l100461 := by
  have f0 : InstrSpec 0x100461 [0x39, 0xE8] (fun s => s.RIP = 0x100461) (cmpR32R32Effect 0x100461 2 0 5)
      [.gpr 0, .gpr 5] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x100461 2 0 5).toInstrSpec (cmp_r32_r32_effect_step 0x100461 0xe8 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100463) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x100463 5 0x7a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100461 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100461 :=
  Rest.liftedBlock (rest_l100461 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100461 x hx)

theorem rest_l100465 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100465 bytes_l100465) (entryMap (live .l100465))
      4 0x100465 bytes_l100465 b_l100465 := by
  have f0 : InstrSpec 0x100465 [0x4C, 0x89, 0x63, 0x08] (StorePre 0x100465 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x100465 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100465 12 (.base 3 (.d8 0x8)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x100465 12 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x100465 0x4c (by decide) 4 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x100469 [0x4C, 0x89, 0x7B, 0x10] (StorePre 0x100469 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x100469 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100469 15 (.base 3 (.d8 0x10)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x100469 15 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x100469 0x4c (by decide) 7 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10046d [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x10046d 6 (fun s => AddrMode.addr (.base 3 .none) s (0x10046d + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x10046d 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x10046d 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x10046d (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100469) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10046d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100473) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 56) (jmp_rel32_effect_step 0x100473 0xffffff24 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100465 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100465 :=
  Rest.liftedBlock (rest_l100465 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100465 x hx)

theorem rest_l100478 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100478 bytes_l100478) (entryMap (live .l100478))
      2 0x100478 bytes_l100478 b_l100478 := by
  have f0 : InstrSpec 0x100478 [0x48, 0x83, 0xC0, 0x0E] (fun s => s.RIP = 0x100478) (addR64Imm8Effect 0x100478 0 0xe)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x100478 0 0xe).toInstrSpec (add_r64_imm8_effect_step 0x100478 0x48 0xc0 0xe (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10047c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x10047c 0x6 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100478 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100478 :=
  Rest.liftedBlock (rest_l100478 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100478 x hx)

theorem rest_l10047e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10047e bytes_l10047e) (entryMap (live .l10047e))
      2 0x10047e bytes_l10047e b_l10047e := by
  have f0 : InstrSpec 0x10047e [0x80, 0x79, 0x01, 0x00] (LoadPre 0x10047e (fun s => AddrMode.addr (.base 1 (.d8 0x1)) s (0x10047e + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x10047e 4 (.base 1 (.d8 0x1)) 0x0)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x10047e 4 (.base 1 (.d8 0x1)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x10047e (.base 1 (.d8 0x1)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (20, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100482) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x100482 8 0x7e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10047e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10047e :=
  Rest.liftedBlock (rest_l10047e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10047e x hx)

theorem rest_l100484 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100484 bytes_l100484) (entryMap (live .l100484))
      6 0x100484 bytes_l100484 b_l100484 := by
  have f0 : InstrSpec 0x100484 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x100484 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x100484 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x100484 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x100484 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x100484 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x100489 [0x41, 0x8B, 0x4E, 0x1C] (LoadPre 0x100489 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x100489 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x100489 1 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x100489 1 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x100489 0x41 (by decide) 1 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10048d [0xC7, 0x03, 0x01, 0x00, 0x00, 0x00] (StorePre 0x10048d 6 (fun s => AddrMode.addr (.base 3 .none) s (0x10048d + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x10048d 6 (.base 3 .none) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x10048d 6 (.base 3 .none) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x10048d (.base 3 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x100493 [0x89, 0x4B, 0x04] (StorePre 0x100493 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x100493 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x100493 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100493 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x100493 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x100496 [0x48, 0x89, 0x43, 0x08] (StorePre 0x100496 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x100496 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100496 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x100496 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x100496 0x48 (by decide) 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100489) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10048d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100493) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100496) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10049a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x10049a 0xfffffefd (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100484 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100484 :=
  Rest.liftedBlock (rest_l100484 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100484 x hx)

theorem rest_l10049f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10049f bytes_l10049f) (entryMap (live .l10049f))
      15 0x10049f bytes_l10049f b_l10049f := by
  have f0 : InstrSpec 0x10049f [0x48, 0x8B, 0x54, 0x24, 0x38] (LoadPre 0x10049f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10049f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10049f 2 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10049f 2 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10049f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1004a4 [0x48, 0x89, 0x53, 0x30] (StorePre 0x1004a4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x1004a4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1004a4 2 (.base 3 (.d8 0x30)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1004a4 2 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1004a4 0x48 (by decide) 2 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1004a8 [0x48, 0x8B, 0x54, 0x24, 0x30] (LoadPre 0x1004a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1004a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1004a8 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1004a8 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1004a8 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1004ad [0x48, 0x89, 0x53, 0x28] (StorePre 0x1004ad 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1004ad + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1004ad 2 (.base 3 (.d8 0x28)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1004ad 2 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1004ad 0x48 (by decide) 2 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1004b1 [0x48, 0x8B, 0x54, 0x24, 0x28] (LoadPre 0x1004b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1004b1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1004b1 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1004b1 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1004b1 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1004b6 [0x48, 0x89, 0x53, 0x20] (StorePre 0x1004b6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1004b6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1004b6 2 (.base 3 (.d8 0x20)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1004b6 2 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1004b6 0x48 (by decide) 2 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1004ba [0x48, 0x8B, 0x54, 0x24, 0x20] (LoadPre 0x1004ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1004ba + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1004ba 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1004ba 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1004ba 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1004bf [0x48, 0x89, 0x53, 0x18] (StorePre 0x1004bf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1004bf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1004bf 2 (.base 3 (.d8 0x18)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1004bf 2 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1004bf 0x48 (by decide) 2 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1004c3 [0x48, 0x8B, 0x54, 0x24, 0x10] (LoadPre 0x1004c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1004c3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1004c3 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1004c3 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1004c3 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1004c8 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x1004c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1004c8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1004c8 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1004c8 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1004c8 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1004cd [0x48, 0x89, 0x73, 0x10] (StorePre 0x1004cd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1004cd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1004cd 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1004cd 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1004cd 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1004d1 [0x48, 0x89, 0x53, 0x08] (StorePre 0x1004d1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1004d1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1004d1 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1004d1 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1004d1 0x48 (by decide) 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1004d5 [0x89, 0x0B] (StorePre 0x1004d5 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1004d5 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1004d5 1 (.base 3 .none))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1004d5 1 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x1004d5 1 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1004d7 [0x89, 0x43, 0x04] (StorePre 0x1004d7 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1004d7 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1004d7 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1004d7 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x1004d7 0 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004a4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004a8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004ad) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004b1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004b6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004ba) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004bf) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004c3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004c8) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004cd) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004d1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004d5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004d7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004da) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 73) (jmp_rel32_effect_step 0x1004da 0xfffffebd (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10049f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10049f :=
  Rest.liftedBlock (rest_l10049f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10049f x hx)

theorem rest_l1004df [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1004df bytes_l1004df) (entryMap (live .l1004df))
      7 0x1004df bytes_l1004df b_l1004df := by
  have f0 : InstrSpec 0x1004df [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x1004df 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1004df + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1004df (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x1004df (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x1004df 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1004e4 [0x41, 0x8B, 0x46, 0x1C] (LoadPre 0x1004e4 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1004e4 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1004e4 0 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR32M32Effect_footprint 0x1004e4 0 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x1004e4 0x41 (by decide) 0 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1004e8 [0xC7, 0x03, 0x01, 0x00, 0x00, 0x00] (StorePre 0x1004e8 6 (fun s => AddrMode.addr (.base 3 .none) s (0x1004e8 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x1004e8 6 (.base 3 .none) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1004e8 6 (.base 3 .none) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x1004e8 (.base 3 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1004ee [0x89, 0x43, 0x04] (StorePre 0x1004ee 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1004ee + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1004ee 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1004ee 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x1004ee 0 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1004f1 [0xC6, 0x43, 0x08, 0x07] (StorePre 0x1004f1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1004f1 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1004f1 (.base 3 (.d8 0x8)) 0x7)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1004f1 (.base 3 (.d8 0x8)) 0x7).toInstrSpec (mov_m8_imm8_effect_step 0x1004f1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide) 0x7) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1004f5 [0x48, 0xC7, 0x43, 0x0C, 0x01, 0x00, 0x00, 0x00] (StorePre 0x1004f5 8 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x1004f5 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1004f5 (.base 3 (.d8 0xc)) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1004f5 (.base 3 (.d8 0xc)) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x1004f5 0x48 (by decide) (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004e4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004e8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004ee) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004f1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004f5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004fd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 60) (jmp_rel32_effect_step 0x1004fd 0xfffffe9a (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1004df [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1004df :=
  Rest.liftedBlock (rest_l1004df code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1004df x hx)

theorem rest_l100502 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100502 bytes_l100502) (entryMap (live .l100502))
      3 0x100502 bytes_l100502 b_l100502 := by
  have f0 : InstrSpec 0x100502 [0x48, 0xFF, 0xC1] (fun s => s.RIP = 0x100502) (incR64Effect 0x100502 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (incR64Effect_footprint 0x100502 1).toInstrSpec (inc_r64_effect_step 0x100502 0x48 0xc1 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100505 [0x49, 0xFF, 0xCF] (fun s => s.RIP = 0x100505) (decR64Effect 0x100505 15)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (decR64Effect_footprint 0x100505 15).toInstrSpec (dec_r64_effect_step 0x100505 0x49 0xcf (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100505) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100508) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel32_effect_step 0x100508 0xfffffedf (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100502 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100502 :=
  Rest.liftedBlock (rest_l100502 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100502 x hx)

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

theorem_by block_l1002f0_eval :
    program.runBlock (dialect code) ⟨.l1002f0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100311_eval :
    program.runBlock (dialect code) ⟨.l100311, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10031a_eval :
    program.runBlock (dialect code) ⟨.l10031a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10032c_eval :
    program.runBlock (dialect code) ⟨.l10032c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100335_eval :
    program.runBlock (dialect code) ⟨.l100335, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10036b_eval :
    program.runBlock (dialect code) ⟨.l10036b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10039c_eval :
    program.runBlock (dialect code) ⟨.l10039c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1003ac_eval :
    program.runBlock (dialect code) ⟨.l1003ac, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1003bf_eval :
    program.runBlock (dialect code) ⟨.l1003bf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1003ca_eval :
    program.runBlock (dialect code) ⟨.l1003ca, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1003d1_eval :
    program.runBlock (dialect code) ⟨.l1003d1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1003d9_eval :
    program.runBlock (dialect code) ⟨.l1003d9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1003e4_eval :
    program.runBlock (dialect code) ⟨.l1003e4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1003ec_eval :
    program.runBlock (dialect code) ⟨.l1003ec, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100400_eval :
    program.runBlock (dialect code) ⟨.l100400, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10040e_eval :
    program.runBlock (dialect code) ⟨.l10040e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100417_eval :
    program.runBlock (dialect code) ⟨.l100417, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100420_eval :
    program.runBlock (dialect code) ⟨.l100420, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10043b_eval :
    program.runBlock (dialect code) ⟨.l10043b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100454_eval :
    program.runBlock (dialect code) ⟨.l100454, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100461_eval :
    program.runBlock (dialect code) ⟨.l100461, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100465_eval :
    program.runBlock (dialect code) ⟨.l100465, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100478_eval :
    program.runBlock (dialect code) ⟨.l100478, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10047e_eval :
    program.runBlock (dialect code) ⟨.l10047e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100484_eval :
    program.runBlock (dialect code) ⟨.l100484, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10049f_eval :
    program.runBlock (dialect code) ⟨.l10049f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1004df_eval :
    program.runBlock (dialect code) ⟨.l1004df, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100502_eval :
    program.runBlock (dialect code) ⟨.l100502, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
