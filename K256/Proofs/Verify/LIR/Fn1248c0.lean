import K256.Proofs.Verify.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

theorem rest_l1248c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1248c0 bytes_l1248c0) (entryMap (live .l1248c0))
      14 0x1248c0 bytes_l1248c0 b_l1248c0 := by
  have f0 : InstrSpec 0x1248c0 [0x41, 0x57] (PushPre 0x1248c0 2) (pushR64Effect 0x1248c0 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1248c0 2 15).toInstrSpec (push_r64_rex_effect_step 0x1248c0 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1248c2 [0x41, 0x56] (PushPre 0x1248c2 2) (pushR64Effect 0x1248c2 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1248c2 2 14).toInstrSpec (push_r64_rex_effect_step 0x1248c2 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1248c4 [0x41, 0x54] (PushPre 0x1248c4 2) (pushR64Effect 0x1248c4 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1248c4 2 12).toInstrSpec (push_r64_rex_effect_step 0x1248c4 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1248c6 [0x53] (PushPre 0x1248c6 1) (pushR64Effect 0x1248c6 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1248c6 1 3).toInstrSpec (push_r64_effect_step 0x1248c6 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1248c7 [0x48, 0x81, 0xEC, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1248c7) (subR64Imm32Effect 0x1248c7 4 0x98)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x1248c7 4 0x98).toInstrSpec (sub_r64_imm32_effect_step 0x1248c7 0x48 0xec 0x98 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1248ce [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x1248ce) (movR64R64Effect 0x1248ce 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1248ce 3 7).toInstrSpec (mov_r64_r64_effect_step 0x1248ce 0x48 0xfb (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1248d1 [0x44, 0x8B, 0x72, 0x08] (LoadPre 0x1248d1 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1248d1 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1248d1 14 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR32M32Effect_footprint 0x1248d1 14 (.base 2 (.d8 0x8))).toInstrSpec (mov_r32_m32_effect_step 0x1248d1 0x44 (by decide) 6 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1248d5 [0x48, 0xC7, 0x84, 0x24, 0x8F, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1248d5 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8f)) s (0x1248d5 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1248d5 (.sib 4 none 0 (.d32 0x8f)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1248d5 (.sib 4 none 0 (.d32 0x8f)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1248d5 0x48 (by decide) (.sib 4 none 0 (.d32 0x8f)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1248e1 [0x48, 0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1248e1 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1248e1 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1248e1 (.sib 4 none 0 (.d32 0x88)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1248e1 (.sib 4 none 0 (.d32 0x88)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1248e1 0x48 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1248ed [0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1248ed 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1248ed + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1248ed (.sib 4 none 0 (.d32 0x80)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1248ed (.sib 4 none 0 (.d32 0x80)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1248ed 0x48 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1248f9 [0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1248f9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1248f9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1248f9 (.sib 4 none 0 (.d8 0x78)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1248f9 (.sib 4 none 0 (.d8 0x78)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1248f9 0x48 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x124902 [0x48, 0xC7, 0x44, 0x24, 0x70, 0x00, 0x00, 0x00, 0x00] (StorePre 0x124902 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x124902 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x124902 (.sib 4 none 0 (.d8 0x70)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x124902 (.sib 4 none 0 (.d8 0x70)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x124902 0x48 (by decide) (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x12490b [0x49, 0x83, 0xFE, 0x28] (fun s => s.RIP = 0x12490b) (cmpR64Imm8Effect 0x12490b 14 0x28)
      [.gpr 14] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x12490b 14 0x28).toInstrSpec (cmp_r64_imm8_effect_step 0x12490b 0x49 0xfe 0x28 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1248c2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1248c4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1248c6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1248c7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1248ce) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 63), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1248d1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 63), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1248d5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(2, 2), (3, 63), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1248e1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 63), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1248ed) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(2, 2), (3, 63), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1248f9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(2, 2), (3, 63), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124902) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(2, 2), (3, 63), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12490b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(2, 2), (3, 63), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (16, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12490f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 74) (jcc_rel32_effect_step 0x12490f 3 0x81) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1248c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1248c0 :=
  Rest.liftedBlock (rest_l1248c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1248c0 x hx)

theorem rest_l124915 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124915 bytes_l124915) (entryMap (live .l124915))
      4 0x124915 bytes_l124915 b_l124915 := by
  have f0 : InstrSpec 0x124915 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x124915) (leaR64Effect 0x124915 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x124915 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x124915 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12491a [0x49, 0x89, 0xF4] (fun s => s.RIP = 0x12491a) (movR64R64Effect 0x12491a 12 6)
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x12491a 12 6).toInstrSpec (mov_r64_r64_effect_step 0x12491a 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12491d [0x44, 0x89, 0xF2] (fun s => s.RIP = 0x12491d) (movR32R32Effect 0x12491d 3 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x12491d 3 2 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x12491d 0x44 0xf2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x124920 [0xE8, 0x5B, 0x32, 0x00, 0x00] (PushPre 0x124920 5) (callEffect (fun _ => 0x127b80) 0x124925)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124920 0x127b80 0x124925).toInstrSpec (call_rel32_effect_step 0x124920 0x325b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12491a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12491d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124920) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l124915 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124915 :=
  Rest.liftedBlock (rest_l124915 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124915 x hx)

theorem rest_l124925 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124925 bytes_l124925) (entryMap (live .l124925))
      3 0x124925 bytes_l124925 b_l124925 := by
  have f0 : InstrSpec 0x124925 [0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x124925 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124925 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124925 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x124925 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x124925 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124929 [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x124929) (cmpR32Imm8Effect 0x124929 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124929 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124929 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124929) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12492c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x12492c 5 0x8a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124925 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124925 :=
  Rest.liftedBlock (rest_l124925 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124925 x hx)

theorem rest_l124932 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124932 bytes_l124932) (entryMap (live .l124932))
      3 0x124932 bytes_l124932 b_l124932 := by
  have f0 : InstrSpec 0x124932 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x124932 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x124932 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124932 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124932 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x124932 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124937 [0x4C, 0x39, 0xF6] (fun s => s.RIP = 0x124937) (cmpR64R64Effect 0x124937 6 14)
      [.gpr 6, .gpr 14] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x124937 6 14).toInstrSpec (cmp_r64_r64_effect_step 0x124937 0x4c 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124937) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12493a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x12493a 5 0x18f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124932 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124932 :=
  Rest.liftedBlock (rest_l124932 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124932 x hx)

theorem rest_l124940 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124940 bytes_l124940) (entryMap (live .l124940))
      5 0x124940 bytes_l124940 b_l124940 := by
  have f0 : InstrSpec 0x124940 [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x124940 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124940 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124940 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124940 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x124940 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124945 [0x4C, 0x8D, 0x7C, 0x24, 0x70] (fun s => s.RIP = 0x124945) (leaR64Effect 0x124945 15 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x124945 15 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (lea_r64_effect_step 0x124945 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12494a [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x12494a) (movR64R64Effect 0x12494a 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12494a 7 15).toInstrSpec (mov_r64_r64_effect_step 0x12494a 0x4c 0xff (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12494d [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x12494d) (movR64R64Effect 0x12494d 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12494d 2 14).toInstrSpec (mov_r64_r64_effect_step 0x12494d 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x124950 [0xFF, 0x15, 0x7A, 0xF4, 0x0D, 0x00] (GoesTo (CallMemPre 0x124950 (.rip 0xdf47a)) (callEffect (callMemPtr 0x124950 (.rip 0xdf47a)) (0x124950 + BitVec.ofNat 64 (callMemLen (.rip 0xdf47a)))) 0x12a820) (callEffect (callMemPtr 0x124950 (.rip 0xdf47a)) (0x124950 + BitVec.ofNat 64 (callMemLen (.rip 0xdf47a))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x124950 (.rip 0xdf47a)).toInstrSpec (call_m64_effect_step 0x124950 (.rip 0xdf47a) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124945) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12494a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12494d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124950) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 3), (4, 61), (5, 5), (6, 53), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l124940 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124940 :=
  Rest.liftedBlock (rest_l124940 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124940 x hx)

theorem rest_l124956 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124956 bytes_l124956) (entryMap (live .l124956))
      4 0x124956 bytes_l124956 b_l124956 := by
  have f0 : InstrSpec 0x124956 [0x48, 0x8D, 0x7C, 0x24, 0x60] (fun s => s.RIP = 0x124956) (leaR64Effect 0x124956 7 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x124956 7 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (lea_r64_effect_step 0x124956 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12495b [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x12495b) (movR64R64Effect 0x12495b 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12495b 6 15).toInstrSpec (mov_r64_r64_effect_step 0x12495b 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12495e [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x12495e) (movR64R64Effect 0x12495e 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12495e 2 14).toInstrSpec (mov_r64_r64_effect_step 0x12495e 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x124961 [0xE8, 0x5A, 0x36, 0x00, 0x00] (PushPre 0x124961 5) (callEffect (fun _ => 0x127fc0) 0x124966)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124961 0x127fc0 0x124966).toInstrSpec (call_rel32_effect_step 0x124961 0x365a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12495b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12495e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124961) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fc0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l124956 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124956 :=
  Rest.liftedBlock (rest_l124956 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124956 x hx)

theorem rest_l124966 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124966 bytes_l124966) (entryMap (live .l124966))
      3 0x124966 bytes_l124966 b_l124966 := by
  have f0 : InstrSpec 0x124966 [0x48, 0x8B, 0x74, 0x24, 0x60] (LoadPre 0x124966 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x124966 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124966 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124966 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x124966 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12496b [0x48, 0x85, 0xF6] (fun s => s.RIP = 0x12496b) (testR64R64Effect 0x12496b 6 6)
      [.gpr 6, .gpr 6] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x12496b 6 6).toInstrSpec (test_r64_r64_effect_step 0x12496b 0x48 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12496b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12496e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x12496e 4 0xf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124966 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124966 :=
  Rest.liftedBlock (rest_l124966 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124966 x hx)

theorem rest_l124970 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124970 bytes_l124970) (entryMap (live .l124970))
      3 0x124970 bytes_l124970 b_l124970 := by
  have f0 : InstrSpec 0x124970 [0x4C, 0x8B, 0x74, 0x24, 0x68] (LoadPre 0x124970 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x124970 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124970 14 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x124970 14 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x124970 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124975 [0x49, 0x83, 0xFE, 0x28] (fun s => s.RIP = 0x124975) (cmpR64Imm8Effect 0x124975 14 0x28)
      [.gpr 14] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x124975 14 0x28).toInstrSpec (cmp_r64_imm8_effect_step 0x124975 0x49 0xfe 0x28 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124975) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124979) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x124979 2 0xb6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124970 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124970 :=
  Rest.liftedBlock (rest_l124970 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124970 x hx)

theorem rest_l12497f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12497f bytes_l12497f) (entryMap (live .l12497f))
      5 0x12497f bytes_l12497f b_l12497f := by
  have f0 : InstrSpec 0x12497f [0x41, 0xC6, 0x44, 0x24, 0x20, 0x01] (StorePre 0x12497f 6 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x20)) s (0x12497f + BitVec.ofNat 64 6)) 1) (movM8Imm8RexEffect 0x12497f (.sib 12 none 0 (.d8 0x20)) 0x1)
      [.gpr 12] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x12497f (.sib 12 none 0 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x12497f 0x41 (by decide) (.sib 12 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x124985 [0x41, 0x8B, 0x44, 0x24, 0x1C] (LoadPre 0x124985 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x1c)) s (0x124985 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x124985 0 (.sib 12 none 0 (.d8 0x1c)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR32M32Effect_footprint 0x124985 0 (.sib 12 none 0 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x124985 0x41 (by decide) 0 (.sib 12 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12498a [0xBA, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12498a) (movR32Imm32Effect 0x12498a 5 2 0x8)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x12498a 5 2 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x12498a 0xba (by decide) 0x8) pre_rip
  have f3 : InstrSpec 0x12498f [0xB9, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12498f) (movR32Imm32Effect 0x12498f 5 1 0x1)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x12498f 5 1 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x12498f 0xb9 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124985) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12498a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (2, 56), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12498f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 54), (1, 58), (2, 56), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124994) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 60) (jmp_rel8_effect_step 0x124994 0x5c (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12497f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12497f :=
  Rest.liftedBlock (rest_l12497f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12497f x hx)

theorem rest_l124996 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124996 bytes_l124996) (entryMap (live .l124996))
      8 0x124996 bytes_l124996 b_l124996 := by
  have f0 : InstrSpec 0x124996 [0x48, 0xC7, 0x44, 0x24, 0x0C, 0x05, 0x00, 0x00, 0x00] (StorePre 0x124996 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x124996 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x124996 (.sib 4 none 0 (.d8 0xc)) 0x5)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x124996 (.sib 4 none 0 (.d8 0xc)) 0x5).toInstrSpec (mov_m64_imm32_effect_step 0x124996 0x48 (by decide) (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide) 0x5) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x12499f [0xC6, 0x44, 0x24, 0x08, 0x05] (StorePre 0x12499f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12499f + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x12499f (.sib 4 none 0 (.d8 0x8)) 0x5)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x12499f (.sib 4 none 0 (.d8 0x8)) 0x5).toInstrSpec (mov_m8_imm8_effect_step 0x12499f (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x5) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1249a4 [0xC6, 0x46, 0x20, 0x01] (StorePre 0x1249a4 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1249a4 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1249a4 (.base 6 (.d8 0x20)) 0x1)
      [.gpr 6] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1249a4 (.base 6 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x1249a4 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1249a8 [0x8B, 0x46, 0x1C] (LoadPre 0x1249a8 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x1249a8 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1249a8 0 (.base 6 (.d8 0x1c)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1249a8 0 (.base 6 (.d8 0x1c))).toInstrSpec (mov_r32_m32_low_effect_step 0x1249a8 0 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1249ab [0x48, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x1249ab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1249ab + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249ab 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1249ab 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1249ab 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1249b0 [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x1249b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1249b0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249b0 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1249b0 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1249b0 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1249b5 [0xB9, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1249b5) (movR32Imm32Effect 0x1249b5 5 1 0x1)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1249b5 5 1 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1249b5 0xb9 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12499f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249a4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249a8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249ab) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249b0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 56), (2, 58), (3, 3), (4, 4), (5, 5), (6, 60), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249b5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 56), (1, 62), (2, 58), (3, 3), (4, 4), (5, 5), (6, 60), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249ba) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 64) (jmp_rel8_effect_step 0x1249ba 0x36 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124996 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124996 :=
  Rest.liftedBlock (rest_l124996 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124996 x hx)

theorem rest_l1249bc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1249bc bytes_l1249bc) (entryMap (live .l1249bc))
      11 0x1249bc bytes_l1249bc b_l1249bc := by
  have f0 : InstrSpec 0x1249bc [0x8B, 0x44, 0x24, 0x0C] (LoadPre 0x1249bc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1249bc + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1249bc 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1249bc 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x1249bc 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1249c0 [0x48, 0x8B, 0x54, 0x24, 0x10] (LoadPre 0x1249c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1249c0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249c0 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1249c0 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1249c0 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1249c5 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x1249c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1249c5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249c5 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1249c5 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1249c5 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1249ca [0x48, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x1249ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1249ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249ca 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1249ca 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1249ca 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1249cf [0x48, 0x89, 0x7C, 0x24, 0x40] (StorePre 0x1249cf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1249cf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1249cf 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1249cf 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x1249cf 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1249d4 [0x48, 0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x1249d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1249d4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249d4 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1249d4 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1249d4 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1249d9 [0x48, 0x89, 0x7C, 0x24, 0x48] (StorePre 0x1249d9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1249d9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1249d9 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1249d9 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x1249d9 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1249de [0x48, 0x8B, 0x7C, 0x24, 0x30] (LoadPre 0x1249de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1249de + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249de 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1249de 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1249de 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1249e3 [0x48, 0x89, 0x7C, 0x24, 0x50] (StorePre 0x1249e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1249e3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1249e3 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1249e3 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x1249e3 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1249e8 [0x48, 0x8B, 0x7C, 0x24, 0x38] (LoadPre 0x1249e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1249e8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249e8 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1249e8 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1249e8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1249ed [0x48, 0x89, 0x7C, 0x24, 0x58] (StorePre 0x1249ed 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1249ed + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1249ed 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1249ed 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x1249ed 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249c0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249c5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249ca) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249cf) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249d4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 62), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249d9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 62), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249de) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 65), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249e3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 65), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249e8) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249ed) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249f2) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 71) (by decide) rfl

theorem block_l1249bc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1249bc :=
  Rest.liftedBlock (rest_l1249bc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1249bc x hx)

theorem rest_l1249f2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1249f2 bytes_l1249f2) (entryMap (live .l1249f2))
      12 0x1249f2 bytes_l1249f2 b_l1249f2 := by
  have f0 : InstrSpec 0x1249f2 [0x48, 0x8B, 0x7C, 0x24, 0x58] (LoadPre 0x1249f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1249f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249f2 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1249f2 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x1249f2 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1249f7 [0x48, 0x89, 0x7B, 0x30] (StorePre 0x1249f7 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x1249f7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1249f7 7 (.base 3 (.d8 0x30)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1249f7 7 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1249f7 0x48 (by decide) 7 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1249fb [0x48, 0x8B, 0x7C, 0x24, 0x50] (LoadPre 0x1249fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1249fb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249fb 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1249fb 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x1249fb 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x124a00 [0x48, 0x89, 0x7B, 0x28] (StorePre 0x124a00 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x124a00 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124a00 7 (.base 3 (.d8 0x28)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124a00 7 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x124a00 0x48 (by decide) 7 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x124a04 [0x48, 0x8B, 0x7C, 0x24, 0x40] (LoadPre 0x124a04 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124a04 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124a04 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x124a04 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x124a04 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x124a09 [0x4C, 0x8B, 0x44, 0x24, 0x48] (LoadPre 0x124a09 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x124a09 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124a09 8 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x124a09 8 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x124a09 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x124a0e [0x4C, 0x89, 0x43, 0x20] (StorePre 0x124a0e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x124a0e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124a0e 8 (.base 3 (.d8 0x20)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124a0e 8 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x124a0e 0x4c (by decide) 0 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x124a12 [0x48, 0x89, 0x7B, 0x18] (StorePre 0x124a12 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x124a12 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124a12 7 (.base 3 (.d8 0x18)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124a12 7 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x124a12 0x48 (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x124a16 [0x89, 0x0B] (StorePre 0x124a16 2 (fun s => AddrMode.addr (.base 3 .none) s (0x124a16 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x124a16 1 (.base 3 .none))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124a16 1 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x124a16 1 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x124a18 [0x89, 0x43, 0x04] (StorePre 0x124a18 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124a18 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124a18 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124a18 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x124a18 0 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x124a1b [0x48, 0x89, 0x53, 0x08] (StorePre 0x124a1b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x124a1b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124a1b 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124a1b 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x124a1b 0x48 (by decide) 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x124a1f [0x48, 0x89, 0x73, 0x10] (StorePre 0x124a1f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x124a1f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124a1f 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124a1f 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x124a1f 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249f7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1249fb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 56), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a00) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 56), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a04) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 59), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a09) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 59), (8, 61), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a0e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 59), (8, 61), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a12) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 59), (8, 61), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a16) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 59), (8, 61), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a18) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 59), (8, 61), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a1b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 59), (8, 61), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a1f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 59), (8, 61), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a23) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 69) (by decide) rfl

theorem block_l1249f2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1249f2 :=
  Rest.liftedBlock (rest_l1249f2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1249f2 x hx)

theorem rest_l124a23 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124a23 bytes_l124a23) (entryMap (live .l124a23))
      7 0x124a23 bytes_l124a23 b_l124a23 := by
  have f0 : InstrSpec 0x124a23 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x124a23) (movR64R64Effect 0x124a23 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x124a23 0 3).toInstrSpec (mov_r64_r64_effect_step 0x124a23 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124a26 [0x48, 0x81, 0xC4, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x124a26) (addR64Imm32Effect 0x124a26 4 0x98)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x124a26 4 0x98).toInstrSpec (add_r64_imm32_effect_step 0x124a26 0x48 0xc4 0x98 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124a2d [0x5B] (PopPre 0x124a2d) (popR64Effect 0x124a2d 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124a2d 1 3).toInstrSpec (pop_r64_effect_step 0x124a2d 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x124a2e [0x41, 0x5C] (PopPre 0x124a2e) (popR64Effect 0x124a2e 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124a2e 2 12).toInstrSpec (pop_r64_rex_effect_step 0x124a2e 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x124a30 [0x41, 0x5E] (PopPre 0x124a30) (popR64Effect 0x124a30 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124a30 2 14).toInstrSpec (pop_r64_rex_effect_step 0x124a30 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x124a32 [0x41, 0x5F] (PopPre 0x124a32) (popR64Effect 0x124a32 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124a32 2 15).toInstrSpec (pop_r64_rex_effect_step 0x124a32 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x124a34 [0xC3] (RetPre 0x124a34) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x124a34).toInstrSpec (ret_effect_step 0x124a34) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a26) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a2d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a2e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a30) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a32) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 63), (15, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a34) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 63), (15, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) f6 (by decide) rfl rfl rfl (by decide)

theorem block_l124a23 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124a23 :=
  Rest.liftedBlock (rest_l124a23 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124a23 x hx)

theorem rest_l124a35 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124a35 bytes_l124a35) (entryMap (live .l124a35))
      8 0x124a35 bytes_l124a35 b_l124a35 := by
  have f0 : InstrSpec 0x124a35 [0x48, 0xC7, 0x44, 0x24, 0x27, 0x00, 0x00, 0x00, 0x00] (StorePre 0x124a35 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x124a35 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x124a35 (.sib 4 none 0 (.d8 0x27)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x124a35 (.sib 4 none 0 (.d8 0x27)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x124a35 0x48 (by decide) (.sib 4 none 0 (.d8 0x27)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x124a3e [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x124a3e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x124a3e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x124a3e (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x124a3e (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x124a3e 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x124a47 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x124a47 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x124a47 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x124a47 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x124a47 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x124a47 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x124a50 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x124a50 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124a50 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x124a50 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x124a50 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x124a50 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x124a59 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x124a59 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124a59 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x124a59 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x124a59 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x124a59 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x124a62 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x124a62) (leaR64Effect 0x124a62 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x124a62 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x124a62 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x124a67 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x124a67) (movR64R64Effect 0x124a67 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x124a67 2 14).toInstrSpec (mov_r64_r64_effect_step 0x124a67 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x124a6a [0xFF, 0x15, 0x60, 0xF3, 0x0D, 0x00] (GoesTo (CallMemPre 0x124a6a (.rip 0xdf360)) (callEffect (callMemPtr 0x124a6a (.rip 0xdf360)) (0x124a6a + BitVec.ofNat 64 (callMemLen (.rip 0xdf360)))) 0x12a820) (callEffect (callMemPtr 0x124a6a (.rip 0xdf360)) (0x124a6a + BitVec.ofNat 64 (callMemLen (.rip 0xdf360))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x124a6a (.rip 0xdf360)).toInstrSpec (call_m64_effect_step 0x124a6a (.rip 0xdf360) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a3e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a47) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a50) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a59) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a62) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a67) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 60), (3, 3), (4, 4), (5, 5), (6, 6), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a6a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(2, 60), (3, 3), (4, 62), (5, 5), (6, 6), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f7 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 64) (by decide) (by decide) rfl rfl

theorem block_l124a35 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124a35 :=
  Rest.liftedBlock (rest_l124a35 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124a35 x hx)

theorem rest_l124a70_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x124a70 bytes_l124a70) [(0, 76), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 65), (9, 70), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x124ac4 bytes_l124a70_1 b_l124a70_1 := by
  have f20 : InstrSpec 0x124ac4 [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x124ac4 6 (fun s => AddrMode.addr (.base 3 .none) s (0x124ac4 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124ac4 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x124ac4 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x124ac4 (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 76), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 65), (9, 70), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124aca) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 85) (jmp_rel32_effect_step 0x124aca 0xffffff54 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l124a70 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124a70 bytes_l124a70) (entryMap (live .l124a70))
      22 0x124a70 bytes_l124a70 b_l124a70 := by
  have f0 : InstrSpec 0x124a70 [0x0F, 0xB7, 0x44, 0x24, 0x08] (LoadPre 0x124a70 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124a70 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x124a70 5 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x124a70 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m16_effect_step 0x124a70 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124a75 [0x48, 0x8B, 0x4C, 0x24, 0x0B] (LoadPre 0x124a75 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x124a75 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124a75 1 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124a75 1 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (mov_r64_m64_effect_step 0x124a75 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124a7a [0x48, 0x8B, 0x54, 0x24, 0x13] (LoadPre 0x124a7a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x124a7a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124a7a 2 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124a7a 2 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (mov_r64_m64_effect_step 0x124a7a 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x124a7f [0x8B, 0x74, 0x24, 0x2B] (LoadPre 0x124a7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2b)) s (0x124a7f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124a7f 6 (.sib 4 none 0 (.d8 0x2b)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x124a7f 6 (.sib 4 none 0 (.d8 0x2b))).toInstrSpec (mov_r32_m32_low_effect_step 0x124a7f 6 (.sib 4 none 0 (.d8 0x2b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x124a83 [0x89, 0x74, 0x24, 0x50] (StorePre 0x124a83 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x124a83 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x124a83 6 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124a83 6 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m32_r32_low_effect_step 0x124a83 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x124a87 [0x48, 0x8B, 0x7C, 0x24, 0x23] (LoadPre 0x124a87 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x23)) s (0x124a87 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124a87 7 (.sib 4 none 0 (.d8 0x23)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x124a87 7 (.sib 4 none 0 (.d8 0x23))).toInstrSpec (mov_r64_m64_effect_step 0x124a87 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x23)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x124a8c [0x48, 0x89, 0x7C, 0x24, 0x48] (StorePre 0x124a8c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x124a8c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124a8c 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124a8c 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x124a8c 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x124a91 [0x4C, 0x8B, 0x44, 0x24, 0x1B] (LoadPre 0x124a91 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x124a91 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124a91 8 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x124a91 8 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (mov_r64_m64_effect_step 0x124a91 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x124a96 [0x4C, 0x89, 0x44, 0x24, 0x40] (StorePre 0x124a96 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124a96 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124a96 8 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124a96 8 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x124a96 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x124a9b [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x0A] (LoadPre 0x124a9b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x124a9b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x124a9b 6 9 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x124a9b 6 9 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x124a9b 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x124aa1 [0x41, 0xC1, 0xE1, 0x18] (fun s => s.RIP = 0x124aa1) (shlR32Effect 0x124aa1 4 9 24)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR32Effect_footprint 0x124aa1 4 9 24).toInstrSpec (shl_r32_imm8_rex_effect_step 0x124aa1 0x41 0xe1 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x124aa5 [0xC1, 0xE0, 0x08] (fun s => s.RIP = 0x124aa5) (shlR32Effect 0x124aa5 3 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x124aa5 3 0 8).toInstrSpec (shl_r32_imm8_effect_step 0x124aa5 0xe0 0x8 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x124aa8 [0x44, 0x09, 0xF0] (fun s => s.RIP = 0x124aa8) (orR32R32Effect 0x124aa8 3 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (orR32R32Effect_footprint 0x124aa8 3 0 14).toInstrSpec (or_r32_r32_rex_effect_step 0x124aa8 0x44 0xf0 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x124aab [0x44, 0x09, 0xC8] (fun s => s.RIP = 0x124aab) (orR32R32Effect 0x124aab 3 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (orR32R32Effect_footprint 0x124aab 3 0 9).toInstrSpec (or_r32_r32_rex_effect_step 0x124aab 0x44 0xc8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x124aae [0x89, 0x73, 0x28] (StorePre 0x124aae 3 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x124aae + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124aae 6 (.base 3 (.d8 0x28)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124aae 6 (.base 3 (.d8 0x28))).toInstrSpec (mov_m32_r32_low_effect_step 0x124aae 6 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x124ab1 [0x48, 0x89, 0x7B, 0x20] (StorePre 0x124ab1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x124ab1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124ab1 7 (.base 3 (.d8 0x20)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124ab1 7 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x124ab1 0x48 (by decide) 7 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x124ab5 [0x4C, 0x89, 0x43, 0x18] (StorePre 0x124ab5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x124ab5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124ab5 8 (.base 3 (.d8 0x18)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124ab5 8 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x124ab5 0x4c (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x124ab9 [0x89, 0x43, 0x04] (StorePre 0x124ab9 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124ab9 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124ab9 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124ab9 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x124ab9 0 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x124abc [0x48, 0x89, 0x4B, 0x08] (StorePre 0x124abc 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x124abc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124abc 1 (.base 3 (.d8 0x8)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124abc 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x124abc 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x124ac0 [0x48, 0x89, 0x53, 0x10] (StorePre 0x124ac0 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x124ac0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124ac0 2 (.base 3 (.d8 0x10)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124ac0 2 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x124ac0 0x48 (by decide) 2 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a75) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a7a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a7f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a83) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a87) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a8c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a91) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 65), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a96) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 65), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124a9b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 65), (9, 68), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124aa1) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 65), (9, 70), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124aa5) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 65), (9, 70), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124aa8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 65), (9, 70), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124aab) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 65), (9, 70), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124aae) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 76), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 65), (9, 70), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ab1) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 76), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 65), (9, 70), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ab5) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 76), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 65), (9, 70), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ab9) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 76), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 65), (9, 70), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124abc) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 76), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 65), (9, 70), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ac0) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 76), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 65), (9, 70), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ac4) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l124a70_1 code

theorem block_l124a70 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124a70 :=
  Rest.liftedBlock (rest_l124a70 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124a70 x hx)

theorem rest_l124acf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124acf bytes_l124acf) (entryMap (live .l124acf))
      3 0x124acf bytes_l124acf b_l124acf := by
  have f0 : InstrSpec 0x124acf [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x124acf) (movR64R64Effect 0x124acf 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x124acf 7 14).toInstrSpec (mov_r64_r64_effect_step 0x124acf 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124ad2 [0x48, 0xC7, 0xC2, 0xE0, 0x36, 0x20, 0x00] (fun s => s.RIP = 0x124ad2) (movR64Imm32Effect 0x124ad2 2 0x2036e0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x124ad2 2 0x2036e0).toInstrSpec (mov_r64_imm32_effect_step 0x124ad2 0x48 0xc2 (by decide) (by decide) (by decide) 0x2036e0) pre_rip
  have f2 : InstrSpec 0x124ad9 [0xE8, 0xB2, 0x51, 0x00, 0x00] (PushPre 0x124ad9 5) (callEffect (fun _ => 0x129c90) 0x124ade)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124ad9 0x129c90 0x124ade).toInstrSpec (call_rel32_effect_step 0x124ad9 0x51b2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 53), (14, 14)]) (p' := 0x124ad2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (4, 4), (5, 5), (6, 6), (7, 53), (14, 14)]) (p' := 0x124ad9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53), (14, 14)]) (p' := 0x129c90) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l124acf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124acf :=
  Rest.liftedBlock (rest_l124acf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124acf x hx)

theorem rest_l124ade [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124ade bytes_l124ade) (entryMap (live .l124ade))
      1 0x124ade bytes_l124ade b_l124ade := by
  have f0 : InstrSpec 0x124ade [0x66, 0x90] (fun s => s.RIP = 0x124ade) (fun _ => nopEffect 0x124ade 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x124ade 2).toInstrSpec (nop_66_effect_step 0x124ade) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ae0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l124ade [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124ade :=
  Rest.liftedBlock (rest_l124ade code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124ade x hx)

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

theorem_by block_l1248c0_eval :
    program.runBlock (dialect code) ⟨.l1248c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124915_eval :
    program.runBlock (dialect code) ⟨.l124915, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124925_eval :
    program.runBlock (dialect code) ⟨.l124925, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124932_eval :
    program.runBlock (dialect code) ⟨.l124932, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124940_eval :
    program.runBlock (dialect code) ⟨.l124940, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124956_eval :
    program.runBlock (dialect code) ⟨.l124956, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124966_eval :
    program.runBlock (dialect code) ⟨.l124966, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124970_eval :
    program.runBlock (dialect code) ⟨.l124970, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12497f_eval :
    program.runBlock (dialect code) ⟨.l12497f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124996_eval :
    program.runBlock (dialect code) ⟨.l124996, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1249bc_eval :
    program.runBlock (dialect code) ⟨.l1249bc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1249f2_eval :
    program.runBlock (dialect code) ⟨.l1249f2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124a23_eval :
    program.runBlock (dialect code) ⟨.l124a23, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124a35_eval :
    program.runBlock (dialect code) ⟨.l124a35, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124a70_eval :
    program.runBlock (dialect code) ⟨.l124a70, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124acf_eval :
    program.runBlock (dialect code) ⟨.l124acf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124ade_eval :
    program.runBlock (dialect code) ⟨.l124ade, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
