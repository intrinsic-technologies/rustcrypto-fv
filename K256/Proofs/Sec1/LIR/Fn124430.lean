import K256.Proofs.Sec1.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Sec1.LIR.Generated.Values

namespace K256.Proofs.Sec1.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

theorem rest_l124430 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124430 bytes_l124430) (entryMap (live .l124430))
      9 0x124430 bytes_l124430 b_l124430 := by
  have f0 : InstrSpec 0x124430 [0x55] (PushPre 0x124430 1) (pushR64Effect 0x124430 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124430 1 5).toInstrSpec (push_r64_effect_step 0x124430 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x124431 [0x41, 0x56] (PushPre 0x124431 2) (pushR64Effect 0x124431 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124431 2 14).toInstrSpec (push_r64_rex_effect_step 0x124431 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x124433 [0x53] (PushPre 0x124433 1) (pushR64Effect 0x124433 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124433 1 3).toInstrSpec (push_r64_effect_step 0x124433 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x124434 [0x48, 0x83, 0xEC, 0x40] (fun s => s.RIP = 0x124434) (subR64Imm8Effect 0x124434 4 0x40)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x124434 4 0x40).toInstrSpec (sub_r64_imm8_effect_step 0x124434 0x48 0xec 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x124438 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x124438) (movR64R64Effect 0x124438 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x124438 14 6).toInstrSpec (mov_r64_r64_effect_step 0x124438 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12443b [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x12443b) (movR64R64Effect 0x12443b 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x12443b 3 7).toInstrSpec (mov_r64_r64_effect_step 0x12443b 0x48 0xfb (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12443e [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x12443e) (leaR64Effect 0x12443e 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x12443e 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x12443e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x124443 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x124443) (movR32Imm32Effect 0x124443 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x124443 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x124443 0xba (by decide) 0x1) pre_rip
  have f8 : InstrSpec 0x124448 [0xE8, 0x33, 0x37, 0x00, 0x00] (PushPre 0x124448 5) (callEffect (fun _ => 0x127b80) 0x12444d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124448 0x127b80 0x12444d).toInstrSpec (call_rel32_effect_step 0x124448 0x3733 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124431) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124433) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124434) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124438) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12443b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12443e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 63), (4, 59), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124443) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 67), (3, 63), (4, 59), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124448) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 67), (3, 63), (4, 69), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l124430 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124430 :=
  Rest.liftedBlock (rest_l124430 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124430 x hx)

theorem rest_l12444d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12444d bytes_l12444d) (entryMap (live .l12444d))
      3 0x12444d bytes_l12444d b_l12444d := by
  have f0 : InstrSpec 0x12444d [0x8B, 0x44, 0x24, 0x08] (LoadPre 0x12444d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12444d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12444d 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x12444d 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x12444d 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124451 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x124451) (cmpR32Imm8Effect 0x124451 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124451 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124451 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124451) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124454) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x124454 5 0x32) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12444d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12444d :=
  Rest.liftedBlock (rest_l12444d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12444d x hx)

theorem rest_l124456 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124456 bytes_l124456) (entryMap (live .l124456))
      3 0x124456 bytes_l124456 b_l124456 := by
  have f0 : InstrSpec 0x124456 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x124456 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x124456 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124456 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124456 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x124456 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12445b [0x48, 0x83, 0xFE, 0x01] (fun s => s.RIP = 0x12445b) (cmpR64Imm8Effect 0x12445b 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x12445b 6 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x12445b 0x48 0xfe 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12445b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12445f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x12445f 5 0x1f8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124456 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124456 :=
  Rest.liftedBlock (rest_l124456 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124456 x hx)

theorem rest_l124465 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124465 bytes_l124465) (entryMap (live .l124465))
      6 0x124465 bytes_l124465 b_l124465 := by
  have f0 : InstrSpec 0x124465 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x124465 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124465 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124465 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x124465 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x124465 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12446a [0x0F, 0xB6, 0x28] (LoadPre 0x12446a (fun s => AddrMode.addr (.base 0 .none) s (0x12446a + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x12446a 3 5 (.base 0 .none))
      [.gpr 0] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x12446a 3 5 (.base 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x12446a 5 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12446d [0x89, 0xE8] (fun s => s.RIP = 0x12446d) (movR32R32Effect 0x12446d 2 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x12446d 2 0 5).toInstrSpec (mov_r32_r32_effect_step 0x12446d 0xe8 (by decide)) pre_rip
  have f3 : InstrSpec 0x12446f [0xFF, 0xC8] (fun s => s.RIP = 0x12446f) (decR32Effect 0x12446f 2 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (decR32Effect_footprint 0x12446f 2 0).toInstrSpec (dec_r32_effect_step 0x12446f 0xc8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x124471 [0x83, 0xF8, 0x30] (fun s => s.RIP = 0x124471) (cmpR32Imm8Effect 0x124471 3 0 0x30)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124471 3 0 0x30).toInstrSpec (cmp_r32_imm8_effect_step 0x124471 0xf8 0x30 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12446a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12446d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12446f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124471) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124474) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel32_effect_step 0x124474 7 0x9e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124465 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124465 :=
  Rest.liftedBlock (rest_l124465 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124465 x hx)

theorem rest_l12447a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12447a bytes_l12447a) (entryMap (live .l12447a))
      0 0x12447a bytes_l12447a b_l12447a := by
  exact Rest.cut

theorem block_l12447a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12447a :=
  Rest.liftedBlock (rest_l12447a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12447a x hx)

theorem rest_l124488 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124488 bytes_l124488) (entryMap (live .l124488))
      16 0x124488 bytes_l124488 b_l124488 := by
  have f0 : InstrSpec 0x124488 [0x8B, 0x4C, 0x24, 0x0C] (LoadPre 0x124488 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x124488 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124488 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x124488 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x124488 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12448c [0x48, 0x8B, 0x54, 0x24, 0x10] (LoadPre 0x12448c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12448c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12448c 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12448c 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x12448c 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124491 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x124491 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x124491 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124491 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124491 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x124491 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x124496 [0x48, 0x8B, 0x7C, 0x24, 0x38] (LoadPre 0x124496 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124496 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124496 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x124496 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x124496 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x12449b [0x48, 0x89, 0x7B, 0x30] (StorePre 0x12449b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x12449b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12449b 7 (.base 3 (.d8 0x30)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12449b 7 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x12449b 0x48 (by decide) 7 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12449f [0x48, 0x8B, 0x7C, 0x24, 0x30] (LoadPre 0x12449f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x12449f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12449f 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12449f 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x12449f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1244a4 [0x48, 0x89, 0x7B, 0x28] (StorePre 0x1244a4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1244a4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1244a4 7 (.base 3 (.d8 0x28)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1244a4 7 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1244a4 0x48 (by decide) 7 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1244a8 [0x48, 0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x1244a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1244a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1244a8 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1244a8 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1244a8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1244ad [0x48, 0x89, 0x7B, 0x20] (StorePre 0x1244ad 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1244ad + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1244ad 7 (.base 3 (.d8 0x20)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1244ad 7 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1244ad 0x48 (by decide) 7 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1244b1 [0x48, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x1244b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1244b1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1244b1 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1244b1 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1244b1 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1244b6 [0x48, 0x89, 0x7B, 0x18] (StorePre 0x1244b6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1244b6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1244b6 7 (.base 3 (.d8 0x18)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1244b6 7 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1244b6 0x48 (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1244ba [0x89, 0x03] (StorePre 0x1244ba 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1244ba + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1244ba 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1244ba 0 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x1244ba 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1244bc [0x89, 0x4B, 0x04] (StorePre 0x1244bc 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1244bc + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1244bc 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1244bc 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x1244bc 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1244bf [0x48, 0x89, 0x53, 0x08] (StorePre 0x1244bf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1244bf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1244bf 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1244bf 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1244bf 0x48 (by decide) 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1244c3 [0x48, 0x89, 0x73, 0x10] (StorePre 0x1244c3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1244c3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1244c3 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1244c3 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1244c3 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12448c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124491) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124496) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12449b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12449f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1244a4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1244a8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1244ad) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1244b1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1244b6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1244ba) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1244bc) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1244bf) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1244c3) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1244c7) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 75) (jmp_rel32_effect_step 0x1244c7 0x9e (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124488 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124488 :=
  Rest.liftedBlock (rest_l124488 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124488 x hx)

theorem rest_l124518 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124518 bytes_l124518) (entryMap (live .l124518))
      2 0x124518 bytes_l124518 b_l124518 := by
  have f0 : InstrSpec 0x124518 [0x40, 0x80, 0xFD, 0x3F] (fun s => s.RIP = 0x124518) (cmpR8Imm8Effect 0x124518 4 5 0x3f)
      [.gpr 5] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x124518 4 5 0x3f).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x124518 0x40 0xfd 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 55) f0 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12451c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x12451c 14 0x6d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124518 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124518 :=
  Rest.liftedBlock (rest_l124518 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124518 x hx)

theorem rest_l12451e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12451e bytes_l12451e) (entryMap (live .l12451e))
      4 0x12451e bytes_l12451e b_l12451e := by
  have f0 : InstrSpec 0x12451e [0x40, 0x0F, 0xB6, 0xF5] (fun s => s.RIP = 0x12451e) (movzxR32R8Effect 0x12451e 4 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movzxR32R8Effect_footprint 0x12451e 4 6 5).toInstrSpec (movzx_r32_r8_rex_effect_step 0x12451e 0x40 (by decide) 0xf5 (by decide)) pre_rip
  have f1 : InstrSpec 0x124522 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x124522) (leaR64Effect 0x124522 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x124522 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x124522 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124527 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x124527) (movR64R64Effect 0x124527 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x124527 2 14).toInstrSpec (mov_r64_r64_effect_step 0x124527 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12452a [0xE8, 0x41, 0x01, 0x00, 0x00] (PushPre 0x12452a 5) (callEffect (fun _ => 0x124670) 0x12452f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12452a 0x124670 0x12452f).toInstrSpec (call_rel32_effect_step 0x12452a 0x141 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124522) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124527) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12452a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124670) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l12451e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12451e :=
  Rest.liftedBlock (rest_l12451e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12451e x hx)

theorem rest_l12452f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12452f bytes_l12452f) (entryMap (live .l12452f))
      4 0x12452f bytes_l12452f b_l12452f := by
  have f0 : InstrSpec 0x12452f [0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x12452f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12452f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12452f 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x12452f 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x12452f 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124533 [0x0F, 0xB6, 0x44, 0x24, 0x0C] (LoadPre 0x124533 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x124533 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x124533 5 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x124533 5 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x124533 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124538 [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x124538) (cmpR32Imm8Effect 0x124538 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124538 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124538 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124533) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124538) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12453b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x12453b 5 0xa7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12452f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12452f :=
  Rest.liftedBlock (rest_l12452f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12452f x hx)

theorem rest_l124541 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124541 bytes_l124541) (entryMap (live .l124541))
      3 0x124541 bytes_l124541 b_l124541 := by
  have f0 : InstrSpec 0x124541 [0x8B, 0x54, 0x24, 0x10] (LoadPre 0x124541 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124541 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124541 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x124541 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x124541 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124545 [0xB1, 0x16] (fun s => s.RIP = 0x124545) (movR8Imm8Effect 0x124545 2 1 0x16)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x124545 2 1 0x16).toInstrSpec (mov_r8_imm8_effect_step 0x124545 0xb1 (by decide) 0x16) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124545) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124547) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x124547 0x6 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124541 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124541 :=
  Rest.liftedBlock (rest_l124541 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124541 x hx)

theorem rest_l12454f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12454f bytes_l12454f) (entryMap (live .l12454f))
      7 0x12454f bytes_l12454f b_l12454f := by
  have f0 : InstrSpec 0x12454f [0x40, 0xC0, 0xED, 0x05] (fun s => s.RIP = 0x12454f) (shrR8Effect 0x12454f 4 5 5)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR8Effect_footprint 0x12454f 4 5 5).toInstrSpec (shr_r8_imm8_rex_effect_step 0x12454f 0x40 0xed 0x5 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124553 [0x40, 0x80, 0xE5, 0x01] (fun s => s.RIP = 0x124553) (andR8Imm8Effect 0x124553 4 5 0x1)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x124553 4 5 0x1).toInstrSpec (and_r8_imm8_rex_effect_step 0x124553 0x40 0xe5 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124557 [0x88, 0x4B, 0x04] (StorePre 0x124557 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124557 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x124557 3 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x124557 3 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m8_r8_effect_step 0x124557 1 (by decide) (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x12455a [0x88, 0x43, 0x05] (StorePre 0x12455a 3 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x12455a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x12455a 3 0 (.base 3 (.d8 0x5)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x12455a 3 0 (.base 3 (.d8 0x5))).toInstrSpec (mov_m8_r8_effect_step 0x12455a 0 (by decide) (.base 3 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12455d [0x89, 0x53, 0x08] (StorePre 0x12455d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12455d + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12455d 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x12455d 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x12455d 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x124560 [0x40, 0x88, 0x6B, 0x0C] (StorePre 0x124560 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x124560 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x124560 4 5 (.base 3 (.d8 0xc)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x124560 4 5 (.base 3 (.d8 0xc))).toInstrSpec (mov_m8_r8_rex_effect_step 0x124560 0x40 (by decide) 5 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x124564 [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x124564 6 (fun s => AddrMode.addr (.base 3 .none) s (0x124564 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124564 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x124564 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x124564 (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124553) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124557) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12455a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12455d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124560) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124564) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12456a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 62) (by decide) rfl

theorem block_l12454f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12454f :=
  Rest.liftedBlock (rest_l12454f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12454f x hx)

theorem rest_l12456a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12456a bytes_l12456a) (entryMap (live .l12456a))
      5 0x12456a bytes_l12456a b_l12456a := by
  have f0 : InstrSpec 0x12456a [0x48, 0x83, 0xC4, 0x40] (fun s => s.RIP = 0x12456a) (addR64Imm8Effect 0x12456a 4 0x40)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12456a 4 0x40).toInstrSpec (add_r64_imm8_effect_step 0x12456a 0x48 0xc4 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12456e [0x5B] (PopPre 0x12456e) (popR64Effect 0x12456e 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12456e 1 3).toInstrSpec (pop_r64_effect_step 0x12456e 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x12456f [0x41, 0x5E] (PopPre 0x12456f) (popR64Effect 0x12456f 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12456f 2 14).toInstrSpec (pop_r64_rex_effect_step 0x12456f 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x124571 [0x5D] (PopPre 0x124571) (popR64Effect 0x124571 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124571 1 5).toInstrSpec (pop_r64_effect_step 0x124571 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x124572 [0xC3] (RetPre 0x124572) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x124572).toInstrSpec (ret_effect_step 0x124572) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12456e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12456f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124571) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (5, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124572) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (5, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l12456a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12456a :=
  Rest.liftedBlock (rest_l12456a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12456a x hx)

theorem rest_l12458b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12458b bytes_l12458b) (entryMap (live .l12458b))
      2 0x12458b bytes_l12458b b_l12458b := by
  have f0 : InstrSpec 0x12458b [0x40, 0x80, 0xFD, 0xC0] (fun s => s.RIP = 0x12458b) (cmpR8Imm8Effect 0x12458b 4 5 0xc0)
      [.gpr 5] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x12458b 4 5 0xc0).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x12458b 0x40 0xfd 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 55) f0 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12458f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x12458f 13 0x27) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12458b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12458b :=
  Rest.liftedBlock (rest_l12458b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12458b x hx)

theorem rest_l124591 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124591 bytes_l124591) (entryMap (live .l124591))
      4 0x124591 bytes_l124591 b_l124591 := by
  have f0 : InstrSpec 0x124591 [0x40, 0x0F, 0xB6, 0xF5] (fun s => s.RIP = 0x124591) (movzxR32R8Effect 0x124591 4 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movzxR32R8Effect_footprint 0x124591 4 6 5).toInstrSpec (movzx_r32_r8_rex_effect_step 0x124591 0x40 (by decide) 0xf5 (by decide)) pre_rip
  have f1 : InstrSpec 0x124595 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x124595) (leaR64Effect 0x124595 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x124595 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x124595 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12459a [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x12459a) (movR64R64Effect 0x12459a 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12459a 2 14).toInstrSpec (mov_r64_r64_effect_step 0x12459a 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12459d [0xE8, 0xCE, 0x00, 0x00, 0x00] (PushPre 0x12459d 5) (callEffect (fun _ => 0x124670) 0x1245a2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12459d 0x124670 0x1245a2).toInstrSpec (call_rel32_effect_step 0x12459d 0xce (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124595) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12459a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12459d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124670) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l124591 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124591 :=
  Rest.liftedBlock (rest_l124591 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124591 x hx)

theorem rest_l1245a2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1245a2 bytes_l1245a2) (entryMap (live .l1245a2))
      4 0x1245a2 bytes_l1245a2 b_l1245a2 := by
  have f0 : InstrSpec 0x1245a2 [0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x1245a2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1245a2 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1245a2 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x1245a2 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x1245a2 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1245a6 [0x0F, 0xB6, 0x44, 0x24, 0x0C] (LoadPre 0x1245a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1245a6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1245a6 5 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1245a6 5 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x1245a6 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1245ab [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x1245ab) (cmpR32Imm8Effect 0x1245ab 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1245ab 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1245ab 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245a6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245ab) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245ae) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x1245ae 5 0x38) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1245a2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1245a2 :=
  Rest.liftedBlock (rest_l1245a2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1245a2 x hx)

theorem rest_l1245b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1245b0 bytes_l1245b0) (entryMap (live .l1245b0))
      3 0x1245b0 bytes_l1245b0 b_l1245b0 := by
  have f0 : InstrSpec 0x1245b0 [0x8B, 0x54, 0x24, 0x10] (LoadPre 0x1245b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1245b0 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1245b0 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1245b0 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x1245b0 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1245b4 [0xB1, 0x17] (fun s => s.RIP = 0x1245b4) (movR8Imm8Effect 0x1245b4 2 1 0x17)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x1245b4 2 1 0x17).toInstrSpec (mov_r8_imm8_effect_step 0x1245b4 0xb1 (by decide) 0x17) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245b4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245b6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x1245b6 0x97 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1245b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1245b0 :=
  Rest.liftedBlock (rest_l1245b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1245b0 x hx)

theorem rest_l1245b8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1245b8 bytes_l1245b8) (entryMap (live .l1245b8))
      1 0x1245b8 bytes_l1245b8 b_l1245b8 := by
  exact Rest.jcc (n := 53) (jcc_rel32_effect_step 0x1245b8 2 0x80) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1245b8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1245b8 :=
  Rest.liftedBlock (rest_l1245b8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1245b8 x hx)

theorem rest_l1245be [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1245be bytes_l1245be) (entryMap (live .l1245be))
      4 0x1245be bytes_l1245be b_l1245be := by
  have f0 : InstrSpec 0x1245be [0x40, 0x0F, 0xB6, 0xF5] (fun s => s.RIP = 0x1245be) (movzxR32R8Effect 0x1245be 4 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movzxR32R8Effect_footprint 0x1245be 4 6 5).toInstrSpec (movzx_r32_r8_rex_effect_step 0x1245be 0x40 (by decide) 0xf5 (by decide)) pre_rip
  have f1 : InstrSpec 0x1245c2 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x1245c2) (leaR64Effect 0x1245c2 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1245c2 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x1245c2 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1245c7 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x1245c7) (movR64R64Effect 0x1245c7 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1245c7 2 14).toInstrSpec (mov_r64_r64_effect_step 0x1245c7 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1245ca [0xE8, 0xA1, 0x00, 0x00, 0x00] (PushPre 0x1245ca 5) (callEffect (fun _ => 0x124670) 0x1245cf)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1245ca 0x124670 0x1245cf).toInstrSpec (call_rel32_effect_step 0x1245ca 0xa1 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245c2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245c7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245ca) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124670) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1245be [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1245be :=
  Rest.liftedBlock (rest_l1245be code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1245be x hx)

theorem rest_l1245cf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1245cf bytes_l1245cf) (entryMap (live .l1245cf))
      4 0x1245cf bytes_l1245cf b_l1245cf := by
  have f0 : InstrSpec 0x1245cf [0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x1245cf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1245cf + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1245cf 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x1245cf 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x1245cf 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1245d3 [0x0F, 0xB6, 0x44, 0x24, 0x0C] (LoadPre 0x1245d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1245d3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1245d3 5 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1245d3 5 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x1245d3 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1245d8 [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x1245d8) (cmpR32Imm8Effect 0x1245d8 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1245d8 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1245d8 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245d3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245d8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245db) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x1245db 5 0xb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1245cf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1245cf :=
  Rest.liftedBlock (rest_l1245cf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1245cf x hx)

theorem rest_l1245dd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1245dd bytes_l1245dd) (entryMap (live .l1245dd))
      3 0x1245dd bytes_l1245dd b_l1245dd := by
  have f0 : InstrSpec 0x1245dd [0x8B, 0x54, 0x24, 0x10] (LoadPre 0x1245dd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1245dd + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1245dd 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1245dd 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x1245dd 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1245e1 [0xB1, 0x18] (fun s => s.RIP = 0x1245e1) (movR8Imm8Effect 0x1245e1 2 1 0x18)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x1245e1 2 1 0x18).toInstrSpec (mov_r8_imm8_effect_step 0x1245e1 0xb1 (by decide) 0x18) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245e1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245e3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel32_effect_step 0x1245e3 0xffffff67 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1245dd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1245dd :=
  Rest.liftedBlock (rest_l1245dd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1245dd x hx)

theorem rest_l1245e8_1 [Bindings] (code : CodeMap) :
    Rest (n := 82) code lifted (codeRange 0x1245e8 bytes_l1245e8) [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 76), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x124639 bytes_l1245e8_1 b_l1245e8_1 := by
  exact Rest.jmp (n := 82) (jmp_rel32_effect_step 0x124639 0xffffff2c (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l1245e8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1245e8 bytes_l1245e8) (entryMap (live .l1245e8))
      21 0x1245e8 bytes_l1245e8 b_l1245e8 := by
  have f0 : InstrSpec 0x1245e8 [0x0F, 0xB6, 0x54, 0x24, 0x0F] (LoadPre 0x1245e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1245e8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1245e8 5 2 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1245e8 5 2 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_effect_step 0x1245e8 2 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1245ed [0x88, 0x53, 0x07] (StorePre 0x1245ed 3 (fun s => AddrMode.addr (.base 3 (.d8 0x7)) s (0x1245ed + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1245ed 3 2 (.base 3 (.d8 0x7)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x1245ed 3 2 (.base 3 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x1245ed 2 (by decide) (.base 3 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1245f0 [0x0F, 0xB7, 0x54, 0x24, 0x0D] (LoadPre 0x1245f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x1245f0 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1245f0 5 2 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x1245f0 5 2 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (movzx_r32_m16_effect_step 0x1245f0 2 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1245f5 [0x66, 0x89, 0x53, 0x05] (StorePre 0x1245f5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x1245f5 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x1245f5 4 2 (.base 3 (.d8 0x5)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x1245f5 4 2 (.base 3 (.d8 0x5))).toInstrSpec (mov_m16_r16_effect_step 0x1245f5 2 (.base 3 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1245f9 [0x8B, 0x54, 0x24, 0x10] (LoadPre 0x1245f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1245f9 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1245f9 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1245f9 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x1245f9 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1245fd [0x48, 0x8B, 0x74, 0x24, 0x1C] (LoadPre 0x1245fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1245fd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1245fd 6 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1245fd 6 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x1245fd 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x124602 [0x48, 0x89, 0x73, 0x14] (StorePre 0x124602 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x124602 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124602 6 (.base 3 (.d8 0x14)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124602 6 (.base 3 (.d8 0x14))).toInstrSpec (mov_m64_r64_effect_step 0x124602 0x48 (by decide) 6 (.base 3 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x124606 [0x48, 0x8B, 0x74, 0x24, 0x24] (LoadPre 0x124606 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x124606 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124606 6 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124606 6 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x124606 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x12460b [0x48, 0x89, 0x73, 0x1C] (StorePre 0x12460b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x12460b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12460b 6 (.base 3 (.d8 0x1c)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12460b 6 (.base 3 (.d8 0x1c))).toInstrSpec (mov_m64_r64_effect_step 0x12460b 0x48 (by decide) 6 (.base 3 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12460f [0x48, 0x8B, 0x74, 0x24, 0x2C] (LoadPre 0x12460f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x12460f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12460f 6 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12460f 6 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x12460f 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x124614 [0x48, 0x89, 0x73, 0x24] (StorePre 0x124614 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x124614 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124614 6 (.base 3 (.d8 0x24)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124614 6 (.base 3 (.d8 0x24))).toInstrSpec (mov_m64_r64_effect_step 0x124614 0x48 (by decide) 6 (.base 3 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x124618 [0x48, 0x8B, 0x74, 0x24, 0x34] (LoadPre 0x124618 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x124618 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124618 6 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124618 6 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r64_m64_effect_step 0x124618 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x12461d [0x48, 0x89, 0x73, 0x2C] (StorePre 0x12461d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x12461d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12461d 6 (.base 3 (.d8 0x2c)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12461d 6 (.base 3 (.d8 0x2c))).toInstrSpec (mov_m64_r64_effect_step 0x12461d 0x48 (by decide) 6 (.base 3 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x124621 [0x8B, 0x74, 0x24, 0x3C] (LoadPre 0x124621 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x124621 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124621 6 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x124621 6 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r32_m32_low_effect_step 0x124621 6 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x124625 [0x89, 0x73, 0x34] (StorePre 0x124625 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x124625 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124625 6 (.base 3 (.d8 0x34)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124625 6 (.base 3 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x124625 6 (.base 3 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x124628 [0x48, 0x8B, 0x74, 0x24, 0x14] (LoadPre 0x124628 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124628 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124628 6 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124628 6 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x124628 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x12462d [0x48, 0x89, 0x73, 0x0C] (StorePre 0x12462d 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x12462d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12462d 6 (.base 3 (.d8 0xc)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12462d 6 (.base 3 (.d8 0xc))).toInstrSpec (mov_m64_r64_effect_step 0x12462d 0x48 (by decide) 6 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x124631 [0x89, 0x0B] (StorePre 0x124631 2 (fun s => AddrMode.addr (.base 3 .none) s (0x124631 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x124631 1 (.base 3 .none))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124631 1 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x124631 1 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x124633 [0x88, 0x43, 0x04] (StorePre 0x124633 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124633 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x124633 3 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x124633 3 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m8_r8_effect_step 0x124633 0 (by decide) (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x124636 [0x89, 0x53, 0x08] (StorePre 0x124636 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x124636 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124636 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124636 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x124636 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245ed) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245f0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245f5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245f9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1245fd) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 61), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124602) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 61), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124606) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12460b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12460f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124614) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124618) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12461d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124621) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124625) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124628) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 76), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12462d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 76), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124631) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 76), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124633) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 76), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124636) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 76), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124639) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1245e8_1 code

theorem block_l1245e8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1245e8 :=
  Rest.liftedBlock (rest_l1245e8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1245e8 x hx)

theorem rest_l12463e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12463e bytes_l12463e) (entryMap (live .l12463e))
      7 0x12463e bytes_l12463e b_l12463e := by
  have f0 : InstrSpec 0x12463e [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x12463e 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x12463e + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x12463e (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x12463e (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x12463e 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x124643 [0x41, 0x8B, 0x46, 0x1C] (LoadPre 0x124643 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x124643 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x124643 0 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR32M32Effect_footprint 0x124643 0 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x124643 0x41 (by decide) 0 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124647 [0xC7, 0x03, 0x01, 0x00, 0x00, 0x00] (StorePre 0x124647 6 (fun s => AddrMode.addr (.base 3 .none) s (0x124647 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124647 6 (.base 3 .none) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x124647 6 (.base 3 .none) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x124647 (.base 3 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x12464d [0x89, 0x43, 0x04] (StorePre 0x12464d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x12464d + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12464d 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x12464d 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x12464d 0 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x124650 [0xC6, 0x43, 0x08, 0x12] (StorePre 0x124650 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x124650 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124650 (.base 3 (.d8 0x8)) 0x12)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x124650 (.base 3 (.d8 0x8)) 0x12).toInstrSpec (mov_m8_imm8_effect_step 0x124650 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide) 0x12) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x124654 [0x40, 0x88, 0x6B, 0x09] (StorePre 0x124654 4 (fun s => AddrMode.addr (.base 3 (.d8 0x9)) s (0x124654 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x124654 4 5 (.base 3 (.d8 0x9)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x124654 4 5 (.base 3 (.d8 0x9))).toInstrSpec (mov_m8_r8_rex_effect_step 0x124654 0x40 (by decide) 5 (.base 3 (.d8 0x9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124643) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124647) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12464d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124650) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124654) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124658) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 60) (jmp_rel32_effect_step 0x124658 0xffffff0d (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12463e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12463e :=
  Rest.liftedBlock (rest_l12463e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12463e x hx)

theorem rest_l12465d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12465d bytes_l12465d) (entryMap (live .l12465d))
      3 0x12465d bytes_l12465d b_l12465d := by
  have f0 : InstrSpec 0x12465d [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12465d) (movR32Imm32Effect 0x12465d 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x12465d 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x12465d 0xbf (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x124662 [0x48, 0xC7, 0xC2, 0xE0, 0x36, 0x20, 0x00] (fun s => s.RIP = 0x124662) (movR64Imm32Effect 0x124662 2 0x2036e0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x124662 2 0x2036e0).toInstrSpec (mov_r64_imm32_effect_step 0x124662 0x48 0xc2 (by decide) (by decide) (by decide) 0x2036e0) pre_rip
  have f2 : InstrSpec 0x124669 [0xE8, 0x22, 0x56, 0x00, 0x00] (PushPre 0x124669 5) (callEffect (fun _ => 0x129c90) 0x12466e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124669 0x129c90 0x12466e).toInstrSpec (call_rel32_effect_step 0x124669 0x5622 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x124662) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x124669) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)]) (p' := 0x129c90) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l12465d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12465d :=
  Rest.liftedBlock (rest_l12465d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12465d x hx)

theorem rest_l12466e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12466e bytes_l12466e) (entryMap (live .l12466e))
      1 0x12466e bytes_l12466e b_l12466e := by
  have f0 : InstrSpec 0x12466e [0x66, 0x90] (fun s => s.RIP = 0x12466e) (fun _ => nopEffect 0x12466e 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12466e 2).toInstrSpec (nop_66_effect_step 0x12466e) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124670) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l12466e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12466e :=
  Rest.liftedBlock (rest_l12466e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12466e x hx)

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

theorem_by block_l124430_eval :
    program.runBlock (dialect code) ⟨.l124430, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12444d_eval :
    program.runBlock (dialect code) ⟨.l12444d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124456_eval :
    program.runBlock (dialect code) ⟨.l124456, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124465_eval :
    program.runBlock (dialect code) ⟨.l124465, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12447a_eval :
    program.runBlock (dialect code) ⟨.l12447a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124488_eval :
    program.runBlock (dialect code) ⟨.l124488, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124518_eval :
    program.runBlock (dialect code) ⟨.l124518, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12451e_eval :
    program.runBlock (dialect code) ⟨.l12451e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12452f_eval :
    program.runBlock (dialect code) ⟨.l12452f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124541_eval :
    program.runBlock (dialect code) ⟨.l124541, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12454f_eval :
    program.runBlock (dialect code) ⟨.l12454f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12456a_eval :
    program.runBlock (dialect code) ⟨.l12456a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12458b_eval :
    program.runBlock (dialect code) ⟨.l12458b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124591_eval :
    program.runBlock (dialect code) ⟨.l124591, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1245a2_eval :
    program.runBlock (dialect code) ⟨.l1245a2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1245b0_eval :
    program.runBlock (dialect code) ⟨.l1245b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1245b8_eval :
    program.runBlock (dialect code) ⟨.l1245b8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1245be_eval :
    program.runBlock (dialect code) ⟨.l1245be, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1245cf_eval :
    program.runBlock (dialect code) ⟨.l1245cf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1245dd_eval :
    program.runBlock (dialect code) ⟨.l1245dd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1245e8_eval :
    program.runBlock (dialect code) ⟨.l1245e8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12463e_eval :
    program.runBlock (dialect code) ⟨.l12463e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12465d_eval :
    program.runBlock (dialect code) ⟨.l12465d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12466e_eval :
    program.runBlock (dialect code) ⟨.l12466e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Sec1.LIR
