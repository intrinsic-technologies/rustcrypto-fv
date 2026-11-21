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

theorem rest_l106900 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106900 bytes_l106900) (entryMap (live .l106900))
      9 0x106900 bytes_l106900 b_l106900 := by
  have f0 : InstrSpec 0x106900 [0x55] (PushPre 0x106900 1) (pushR64Effect 0x106900 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106900 1 5).toInstrSpec (push_r64_effect_step 0x106900 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x106901 [0x41, 0x56] (PushPre 0x106901 2) (pushR64Effect 0x106901 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106901 2 14).toInstrSpec (push_r64_rex_effect_step 0x106901 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x106903 [0x53] (PushPre 0x106903 1) (pushR64Effect 0x106903 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106903 1 3).toInstrSpec (push_r64_effect_step 0x106903 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x106904 [0x48, 0x83, 0xEC, 0x40] (fun s => s.RIP = 0x106904) (subR64Imm8Effect 0x106904 4 0x40)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x106904 4 0x40).toInstrSpec (sub_r64_imm8_effect_step 0x106904 0x48 0xec 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x106908 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x106908) (movR64R64Effect 0x106908 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x106908 14 6).toInstrSpec (mov_r64_r64_effect_step 0x106908 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10690b [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x10690b) (movR64R64Effect 0x10690b 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10690b 3 7).toInstrSpec (mov_r64_r64_effect_step 0x10690b 0x48 0xfb (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10690e [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x10690e) (leaR64Effect 0x10690e 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10690e 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10690e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x106913 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106913) (movR32Imm32Effect 0x106913 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x106913 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x106913 0xba (by decide) 0x1) pre_rip
  have f8 : InstrSpec 0x106918 [0xE8, 0x63, 0x12, 0x02, 0x00] (PushPre 0x106918 5) (callEffect (fun _ => 0x127b80) 0x10691d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106918 0x127b80 0x10691d).toInstrSpec (call_rel32_effect_step 0x106918 0x21263 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106901) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106903) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106904) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106908) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10690b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10690e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 63), (4, 59), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106913) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 67), (3, 63), (4, 59), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106918) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 67), (3, 63), (4, 69), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l106900 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106900 :=
  Rest.liftedBlock (rest_l106900 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106900 x hx)

theorem rest_l10691d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10691d bytes_l10691d) (entryMap (live .l10691d))
      3 0x10691d bytes_l10691d b_l10691d := by
  have f0 : InstrSpec 0x10691d [0x8B, 0x44, 0x24, 0x08] (LoadPre 0x10691d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10691d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10691d 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x10691d 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x10691d 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106921 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x106921) (cmpR32Imm8Effect 0x106921 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x106921 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x106921 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106921) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106924) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x106924 5 0x32) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10691d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10691d :=
  Rest.liftedBlock (rest_l10691d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10691d x hx)

theorem rest_l106926 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106926 bytes_l106926) (entryMap (live .l106926))
      3 0x106926 bytes_l106926 b_l106926 := by
  have f0 : InstrSpec 0x106926 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x106926 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x106926 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106926 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x106926 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x106926 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10692b [0x48, 0x83, 0xFE, 0x01] (fun s => s.RIP = 0x10692b) (cmpR64Imm8Effect 0x10692b 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x10692b 6 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x10692b 0x48 0xfe 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10692b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10692f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x10692f 5 0x210) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106926 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106926 :=
  Rest.liftedBlock (rest_l106926 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106926 x hx)

theorem rest_l106935 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106935 bytes_l106935) (entryMap (live .l106935))
      6 0x106935 bytes_l106935 b_l106935 := by
  have f0 : InstrSpec 0x106935 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x106935 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106935 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106935 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x106935 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x106935 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10693a [0x0F, 0xB6, 0x28] (LoadPre 0x10693a (fun s => AddrMode.addr (.base 0 .none) s (0x10693a + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x10693a 3 5 (.base 0 .none))
      [.gpr 0] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x10693a 3 5 (.base 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x10693a 5 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10693d [0x89, 0xE8] (fun s => s.RIP = 0x10693d) (movR32R32Effect 0x10693d 2 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x10693d 2 0 5).toInstrSpec (mov_r32_r32_effect_step 0x10693d 0xe8 (by decide)) pre_rip
  have f3 : InstrSpec 0x10693f [0xFF, 0xC8] (fun s => s.RIP = 0x10693f) (decR32Effect 0x10693f 2 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (decR32Effect_footprint 0x10693f 2 0).toInstrSpec (dec_r32_effect_step 0x10693f 0xc8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x106941 [0x83, 0xF8, 0x30] (fun s => s.RIP = 0x106941) (cmpR32Imm8Effect 0x106941 3 0 0x30)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x106941 3 0 0x30).toInstrSpec (cmp_r32_imm8_effect_step 0x106941 0xf8 0x30 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10693a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10693d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10693f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106941) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106944) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel32_effect_step 0x106944 7 0xb3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106935 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106935 :=
  Rest.liftedBlock (rest_l106935 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106935 x hx)

theorem rest_l10694a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10694a bytes_l10694a) (entryMap (live .l10694a))
      0 0x10694a bytes_l10694a b_l10694a := by
  exact Rest.cut

theorem block_l10694a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10694a :=
  Rest.liftedBlock (rest_l10694a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10694a x hx)

theorem rest_l106958_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x106958 bytes_l106958) [(0, 0), (1, 77), (2, 55), (3, 3), (4, 4), (6, 57), (7, 71), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x1069a8 bytes_l106958_1 b_l106958_1 := by
  have f20 : InstrSpec 0x1069a8 [0x40, 0x88, 0x7B, 0x04] (StorePre 0x1069a8 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1069a8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1069a8 4 7 (.base 3 (.d8 0x4)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x1069a8 4 7 (.base 3 (.d8 0x4))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1069a8 0x40 (by decide) 7 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 77), (2, 55), (3, 3), (4, 4), (6, 57), (7, 71), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069ac) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 85) (jmp_rel32_effect_step 0x1069ac 0x9e (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l106958 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106958 bytes_l106958) (entryMap (live .l106958))
      22 0x106958 bytes_l106958 b_l106958 := by
  have f0 : InstrSpec 0x106958 [0x8B, 0x4C, 0x24, 0x0C] (LoadPre 0x106958 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106958 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106958 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x106958 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x106958 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10695c [0x48, 0x8B, 0x54, 0x24, 0x10] (LoadPre 0x10695c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10695c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10695c 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10695c 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10695c 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106961 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x106961 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x106961 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106961 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x106961 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x106961 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x106966 [0x48, 0x8B, 0x7C, 0x24, 0x38] (LoadPre 0x106966 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x106966 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106966 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x106966 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x106966 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10696b [0x48, 0x89, 0x7B, 0x30] (StorePre 0x10696b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x10696b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10696b 7 (.base 3 (.d8 0x30)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10696b 7 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10696b 0x48 (by decide) 7 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10696f [0x48, 0x8B, 0x7C, 0x24, 0x30] (LoadPre 0x10696f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10696f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10696f 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10696f 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10696f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x106974 [0x48, 0x89, 0x7B, 0x28] (StorePre 0x106974 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x106974 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106974 7 (.base 3 (.d8 0x28)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106974 7 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x106974 0x48 (by decide) 7 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x106978 [0x48, 0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x106978 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106978 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106978 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x106978 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x106978 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10697d [0x48, 0x89, 0x7B, 0x20] (StorePre 0x10697d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x10697d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10697d 7 (.base 3 (.d8 0x20)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10697d 7 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10697d 0x48 (by decide) 7 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x106981 [0x48, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x106981 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x106981 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106981 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x106981 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x106981 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x106986 [0x48, 0x89, 0x7B, 0x18] (StorePre 0x106986 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x106986 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106986 7 (.base 3 (.d8 0x18)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106986 7 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x106986 0x48 (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x10698a [0x89, 0xCF] (fun s => s.RIP = 0x10698a) (movR32R32Effect 0x10698a 2 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x10698a 2 7 1).toInstrSpec (mov_r32_r32_effect_step 0x10698a 0xcf (by decide)) pre_rip
  have f12 : InstrSpec 0x10698c [0x41, 0x89, 0xC8] (fun s => s.RIP = 0x10698c) (movR32R32Effect 0x10698c 3 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x10698c 3 8 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x10698c 0x41 0xc8 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10698f [0x41, 0xC1, 0xE8, 0x08] (fun s => s.RIP = 0x10698f) (shrR32Effect 0x10698f 4 8 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR32Effect_footprint 0x10698f 4 8 8).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10698f 0x41 0xe8 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x106993 [0xC1, 0xE9, 0x18] (fun s => s.RIP = 0x106993) (shrR32Effect 0x106993 3 1 24)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x106993 3 1 24).toInstrSpec (shr_r32_imm8_effect_step 0x106993 0xe9 0x18 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x106996 [0x88, 0x4B, 0x07] (StorePre 0x106996 3 (fun s => AddrMode.addr (.base 3 (.d8 0x7)) s (0x106996 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x106996 3 1 (.base 3 (.d8 0x7)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x106996 3 1 (.base 3 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x106996 1 (by decide) (.base 3 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x106999 [0x66, 0x44, 0x89, 0x43, 0x05] (StorePre 0x106999 5 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x106999 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106999 5 8 (.base 3 (.d8 0x5)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x106999 5 8 (.base 3 (.d8 0x5))).toInstrSpec (mov_m16_r16_rex_effect_step 0x106999 0x44 (by decide) 0 (.base 3 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x10699e [0x48, 0x89, 0x53, 0x08] (StorePre 0x10699e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10699e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10699e 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10699e 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10699e 0x48 (by decide) 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1069a2 [0x48, 0x89, 0x73, 0x10] (StorePre 0x1069a2 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1069a2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1069a2 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1069a2 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1069a2 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1069a6 [0x89, 0x03] (StorePre 0x1069a6 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1069a6 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1069a6 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1069a6 0 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x1069a6 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10695c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106961) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106966) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10696b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10696f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106974) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106978) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10697d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106981) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106986) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10698a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 71), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10698c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 71), (8, 73), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10698f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 71), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106993) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 77), (2, 55), (3, 3), (4, 4), (6, 57), (7, 71), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106996) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 77), (2, 55), (3, 3), (4, 4), (6, 57), (7, 71), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106999) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 77), (2, 55), (3, 3), (4, 4), (6, 57), (7, 71), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10699e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 77), (2, 55), (3, 3), (4, 4), (6, 57), (7, 71), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069a2) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 77), (2, 55), (3, 3), (4, 4), (6, 57), (7, 71), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069a6) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 77), (2, 55), (3, 3), (4, 4), (6, 57), (7, 71), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069a8) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l106958_1 code

theorem block_l106958 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106958 :=
  Rest.liftedBlock (rest_l106958 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106958 x hx)

theorem rest_l1069fd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1069fd bytes_l1069fd) (entryMap (live .l1069fd))
      2 0x1069fd bytes_l1069fd b_l1069fd := by
  have f0 : InstrSpec 0x1069fd [0x40, 0x80, 0xFD, 0x3F] (fun s => s.RIP = 0x1069fd) (cmpR8Imm8Effect 0x1069fd 4 5 0x3f)
      [.gpr 5] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x1069fd 4 5 0x3f).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x1069fd 0x40 0xfd 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 55) f0 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a01) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x106a01 14 0x70) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1069fd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1069fd :=
  Rest.liftedBlock (rest_l1069fd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1069fd x hx)

theorem rest_l106a03 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106a03 bytes_l106a03) (entryMap (live .l106a03))
      4 0x106a03 bytes_l106a03 b_l106a03 := by
  have f0 : InstrSpec 0x106a03 [0x40, 0x0F, 0xB6, 0xF5] (fun s => s.RIP = 0x106a03) (movzxR32R8Effect 0x106a03 4 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movzxR32R8Effect_footprint 0x106a03 4 6 5).toInstrSpec (movzx_r32_r8_rex_effect_step 0x106a03 0x40 (by decide) 0xf5 (by decide)) pre_rip
  have f1 : InstrSpec 0x106a07 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x106a07) (leaR64Effect 0x106a07 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x106a07 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x106a07 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106a0c [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x106a0c) (movR64R64Effect 0x106a0c 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x106a0c 2 14).toInstrSpec (mov_r64_r64_effect_step 0x106a0c 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x106a0f [0xE8, 0x4C, 0x01, 0x00, 0x00] (PushPre 0x106a0f 5) (callEffect (fun _ => 0x106b60) 0x106a14)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106a0f 0x106b60 0x106a14).toInstrSpec (call_rel32_effect_step 0x106a0f 0x14c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a07) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a0c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a0f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b60) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l106a03 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106a03 :=
  Rest.liftedBlock (rest_l106a03 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106a03 x hx)

theorem rest_l106a14 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106a14 bytes_l106a14) (entryMap (live .l106a14))
      4 0x106a14 bytes_l106a14 b_l106a14 := by
  have f0 : InstrSpec 0x106a14 [0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x106a14 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106a14 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106a14 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x106a14 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x106a14 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106a18 [0x0F, 0xB6, 0x44, 0x24, 0x0C] (LoadPre 0x106a18 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106a18 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106a18 5 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x106a18 5 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x106a18 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106a1d [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x106a1d) (cmpR32Imm8Effect 0x106a1d 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x106a1d 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x106a1d 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a18) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a1d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a20) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x106a20 5 0xaa) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106a14 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106a14 :=
  Rest.liftedBlock (rest_l106a14 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106a14 x hx)

theorem rest_l106a26 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106a26 bytes_l106a26) (entryMap (live .l106a26))
      3 0x106a26 bytes_l106a26 b_l106a26 := by
  have f0 : InstrSpec 0x106a26 [0x8B, 0x54, 0x24, 0x10] (LoadPre 0x106a26 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106a26 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106a26 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x106a26 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x106a26 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106a2a [0xB1, 0x16] (fun s => s.RIP = 0x106a2a) (movR8Imm8Effect 0x106a2a 2 1 0x16)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x106a2a 2 1 0x16).toInstrSpec (mov_r8_imm8_effect_step 0x106a2a 0xb1 (by decide) 0x16) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a2a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a2c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x106a2c 0x6 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l106a26 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106a26 :=
  Rest.liftedBlock (rest_l106a26 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106a26 x hx)

theorem rest_l106a34 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106a34 bytes_l106a34) (entryMap (live .l106a34))
      7 0x106a34 bytes_l106a34 b_l106a34 := by
  have f0 : InstrSpec 0x106a34 [0x40, 0xC0, 0xED, 0x05] (fun s => s.RIP = 0x106a34) (shrR8Effect 0x106a34 4 5 5)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR8Effect_footprint 0x106a34 4 5 5).toInstrSpec (shr_r8_imm8_rex_effect_step 0x106a34 0x40 0xed 0x5 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106a38 [0x40, 0x80, 0xE5, 0x01] (fun s => s.RIP = 0x106a38) (andR8Imm8Effect 0x106a38 4 5 0x1)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x106a38 4 5 0x1).toInstrSpec (and_r8_imm8_rex_effect_step 0x106a38 0x40 0xe5 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106a3c [0x88, 0x4B, 0x04] (StorePre 0x106a3c 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106a3c + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x106a3c 3 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x106a3c 3 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m8_r8_effect_step 0x106a3c 1 (by decide) (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x106a3f [0x88, 0x43, 0x05] (StorePre 0x106a3f 3 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x106a3f + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x106a3f 3 0 (.base 3 (.d8 0x5)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x106a3f 3 0 (.base 3 (.d8 0x5))).toInstrSpec (mov_m8_r8_effect_step 0x106a3f 0 (by decide) (.base 3 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x106a42 [0x89, 0x53, 0x08] (StorePre 0x106a42 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x106a42 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106a42 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x106a42 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x106a42 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x106a45 [0x40, 0x88, 0x6B, 0x0C] (StorePre 0x106a45 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x106a45 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106a45 4 5 (.base 3 (.d8 0xc)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x106a45 4 5 (.base 3 (.d8 0xc))).toInstrSpec (mov_m8_r8_rex_effect_step 0x106a45 0x40 (by decide) 5 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x106a49 [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x106a49 6 (fun s => AddrMode.addr (.base 3 .none) s (0x106a49 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x106a49 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x106a49 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x106a49 (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a38) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a3c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a3f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a42) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a45) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a49) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a4f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 62) (by decide) rfl

theorem block_l106a34 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106a34 :=
  Rest.liftedBlock (rest_l106a34 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106a34 x hx)

theorem rest_l106a4f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106a4f bytes_l106a4f) (entryMap (live .l106a4f))
      6 0x106a4f bytes_l106a4f b_l106a4f := by
  have f0 : InstrSpec 0x106a4f [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x106a4f) (movR64R64Effect 0x106a4f 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x106a4f 0 3).toInstrSpec (mov_r64_r64_effect_step 0x106a4f 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106a52 [0x48, 0x83, 0xC4, 0x40] (fun s => s.RIP = 0x106a52) (addR64Imm8Effect 0x106a52 4 0x40)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x106a52 4 0x40).toInstrSpec (add_r64_imm8_effect_step 0x106a52 0x48 0xc4 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106a56 [0x5B] (PopPre 0x106a56) (popR64Effect 0x106a56 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106a56 1 3).toInstrSpec (pop_r64_effect_step 0x106a56 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x106a57 [0x41, 0x5E] (PopPre 0x106a57) (popR64Effect 0x106a57 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106a57 2 14).toInstrSpec (pop_r64_rex_effect_step 0x106a57 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x106a59 [0x5D] (PopPre 0x106a59) (popR64Effect 0x106a59 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106a59 1 5).toInstrSpec (pop_r64_effect_step 0x106a59 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x106a5a [0xC3] (RetPre 0x106a5a) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x106a5a).toInstrSpec (ret_effect_step 0x106a5a) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a52) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a56) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a57) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a59) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a5a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l106a4f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106a4f :=
  Rest.liftedBlock (rest_l106a4f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106a4f x hx)

theorem rest_l106a73 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106a73 bytes_l106a73) (entryMap (live .l106a73))
      2 0x106a73 bytes_l106a73 b_l106a73 := by
  have f0 : InstrSpec 0x106a73 [0x40, 0x80, 0xFD, 0xC0] (fun s => s.RIP = 0x106a73) (cmpR8Imm8Effect 0x106a73 4 5 0xc0)
      [.gpr 5] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x106a73 4 5 0xc0).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x106a73 0x40 0xfd 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 55) f0 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a77) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x106a77 13 0x27) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106a73 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106a73 :=
  Rest.liftedBlock (rest_l106a73 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106a73 x hx)

theorem rest_l106a79 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106a79 bytes_l106a79) (entryMap (live .l106a79))
      4 0x106a79 bytes_l106a79 b_l106a79 := by
  have f0 : InstrSpec 0x106a79 [0x40, 0x0F, 0xB6, 0xF5] (fun s => s.RIP = 0x106a79) (movzxR32R8Effect 0x106a79 4 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movzxR32R8Effect_footprint 0x106a79 4 6 5).toInstrSpec (movzx_r32_r8_rex_effect_step 0x106a79 0x40 (by decide) 0xf5 (by decide)) pre_rip
  have f1 : InstrSpec 0x106a7d [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x106a7d) (leaR64Effect 0x106a7d 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x106a7d 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x106a7d 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106a82 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x106a82) (movR64R64Effect 0x106a82 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x106a82 2 14).toInstrSpec (mov_r64_r64_effect_step 0x106a82 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x106a85 [0xE8, 0xD6, 0x00, 0x00, 0x00] (PushPre 0x106a85 5) (callEffect (fun _ => 0x106b60) 0x106a8a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106a85 0x106b60 0x106a8a).toInstrSpec (call_rel32_effect_step 0x106a85 0xd6 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a7d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a82) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a85) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b60) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l106a79 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106a79 :=
  Rest.liftedBlock (rest_l106a79 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106a79 x hx)

theorem rest_l106a8a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106a8a bytes_l106a8a) (entryMap (live .l106a8a))
      4 0x106a8a bytes_l106a8a b_l106a8a := by
  have f0 : InstrSpec 0x106a8a [0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x106a8a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106a8a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106a8a 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x106a8a 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x106a8a 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106a8e [0x0F, 0xB6, 0x44, 0x24, 0x0C] (LoadPre 0x106a8e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106a8e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106a8e 5 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x106a8e 5 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x106a8e 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106a93 [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x106a93) (cmpR32Imm8Effect 0x106a93 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x106a93 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x106a93 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a8e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a93) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a96) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x106a96 5 0x38) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106a8a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106a8a :=
  Rest.liftedBlock (rest_l106a8a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106a8a x hx)

theorem rest_l106a98 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106a98 bytes_l106a98) (entryMap (live .l106a98))
      3 0x106a98 bytes_l106a98 b_l106a98 := by
  have f0 : InstrSpec 0x106a98 [0x8B, 0x54, 0x24, 0x10] (LoadPre 0x106a98 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106a98 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106a98 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x106a98 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x106a98 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106a9c [0xB1, 0x17] (fun s => s.RIP = 0x106a9c) (movR8Imm8Effect 0x106a9c 2 1 0x17)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x106a9c 2 1 0x17).toInstrSpec (mov_r8_imm8_effect_step 0x106a9c 0xb1 (by decide) 0x17) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a9c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a9e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x106a9e 0x94 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l106a98 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106a98 :=
  Rest.liftedBlock (rest_l106a98 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106a98 x hx)

theorem rest_l106aa0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106aa0 bytes_l106aa0) (entryMap (live .l106aa0))
      1 0x106aa0 bytes_l106aa0 b_l106aa0 := by
  exact Rest.jcc (n := 53) (jcc_rel32_effect_step 0x106aa0 2 0x80) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106aa0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106aa0 :=
  Rest.liftedBlock (rest_l106aa0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106aa0 x hx)

theorem rest_l106aa6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106aa6 bytes_l106aa6) (entryMap (live .l106aa6))
      4 0x106aa6 bytes_l106aa6 b_l106aa6 := by
  have f0 : InstrSpec 0x106aa6 [0x40, 0x0F, 0xB6, 0xF5] (fun s => s.RIP = 0x106aa6) (movzxR32R8Effect 0x106aa6 4 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movzxR32R8Effect_footprint 0x106aa6 4 6 5).toInstrSpec (movzx_r32_r8_rex_effect_step 0x106aa6 0x40 (by decide) 0xf5 (by decide)) pre_rip
  have f1 : InstrSpec 0x106aaa [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x106aaa) (leaR64Effect 0x106aaa 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x106aaa 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x106aaa 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106aaf [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x106aaf) (movR64R64Effect 0x106aaf 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x106aaf 2 14).toInstrSpec (mov_r64_r64_effect_step 0x106aaf 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x106ab2 [0xE8, 0xA9, 0x00, 0x00, 0x00] (PushPre 0x106ab2 5) (callEffect (fun _ => 0x106b60) 0x106ab7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106ab2 0x106b60 0x106ab7).toInstrSpec (call_rel32_effect_step 0x106ab2 0xa9 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106aaa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106aaf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ab2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b60) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l106aa6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106aa6 :=
  Rest.liftedBlock (rest_l106aa6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106aa6 x hx)

theorem rest_l106ab7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106ab7 bytes_l106ab7) (entryMap (live .l106ab7))
      4 0x106ab7 bytes_l106ab7 b_l106ab7 := by
  have f0 : InstrSpec 0x106ab7 [0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x106ab7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106ab7 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106ab7 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x106ab7 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x106ab7 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106abb [0x0F, 0xB6, 0x44, 0x24, 0x0C] (LoadPre 0x106abb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106abb + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106abb 5 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x106abb 5 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x106abb 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106ac0 [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x106ac0) (cmpR32Imm8Effect 0x106ac0 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x106ac0 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x106ac0 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106abb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ac0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ac3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x106ac3 5 0xb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106ab7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106ab7 :=
  Rest.liftedBlock (rest_l106ab7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106ab7 x hx)

theorem rest_l106ac5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106ac5 bytes_l106ac5) (entryMap (live .l106ac5))
      3 0x106ac5 bytes_l106ac5 b_l106ac5 := by
  have f0 : InstrSpec 0x106ac5 [0x8B, 0x54, 0x24, 0x10] (LoadPre 0x106ac5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106ac5 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106ac5 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x106ac5 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x106ac5 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106ac9 [0xB1, 0x18] (fun s => s.RIP = 0x106ac9) (movR8Imm8Effect 0x106ac9 2 1 0x18)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x106ac9 2 1 0x18).toInstrSpec (mov_r8_imm8_effect_step 0x106ac9 0xb1 (by decide) 0x18) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ac9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106acb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel32_effect_step 0x106acb 0xffffff64 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l106ac5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106ac5 :=
  Rest.liftedBlock (rest_l106ac5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106ac5 x hx)

theorem rest_l106ad0_1 [Bindings] (code : CodeMap) :
    Rest (n := 82) code lifted (codeRange 0x106ad0 bytes_l106ad0) [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 76), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x106b21 bytes_l106ad0_1 b_l106ad0_1 := by
  exact Rest.jmp (n := 82) (jmp_rel32_effect_step 0x106b21 0xffffff29 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l106ad0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106ad0 bytes_l106ad0) (entryMap (live .l106ad0))
      21 0x106ad0 bytes_l106ad0 b_l106ad0 := by
  have f0 : InstrSpec 0x106ad0 [0x0F, 0xB6, 0x54, 0x24, 0x0F] (LoadPre 0x106ad0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x106ad0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106ad0 5 2 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x106ad0 5 2 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_effect_step 0x106ad0 2 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106ad5 [0x88, 0x53, 0x07] (StorePre 0x106ad5 3 (fun s => AddrMode.addr (.base 3 (.d8 0x7)) s (0x106ad5 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x106ad5 3 2 (.base 3 (.d8 0x7)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x106ad5 3 2 (.base 3 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x106ad5 2 (by decide) (.base 3 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x106ad8 [0x0F, 0xB7, 0x54, 0x24, 0x0D] (LoadPre 0x106ad8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x106ad8 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106ad8 5 2 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x106ad8 5 2 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (movzx_r32_m16_effect_step 0x106ad8 2 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x106add [0x66, 0x89, 0x53, 0x05] (StorePre 0x106add 4 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x106add + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x106add 4 2 (.base 3 (.d8 0x5)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x106add 4 2 (.base 3 (.d8 0x5))).toInstrSpec (mov_m16_r16_effect_step 0x106add 2 (.base 3 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x106ae1 [0x8B, 0x54, 0x24, 0x10] (LoadPre 0x106ae1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106ae1 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106ae1 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x106ae1 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x106ae1 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x106ae5 [0x48, 0x8B, 0x74, 0x24, 0x1C] (LoadPre 0x106ae5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x106ae5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106ae5 6 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x106ae5 6 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x106ae5 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x106aea [0x48, 0x89, 0x73, 0x14] (StorePre 0x106aea 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x106aea + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106aea 6 (.base 3 (.d8 0x14)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106aea 6 (.base 3 (.d8 0x14))).toInstrSpec (mov_m64_r64_effect_step 0x106aea 0x48 (by decide) 6 (.base 3 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x106aee [0x48, 0x8B, 0x74, 0x24, 0x24] (LoadPre 0x106aee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x106aee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106aee 6 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x106aee 6 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x106aee 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x106af3 [0x48, 0x89, 0x73, 0x1C] (StorePre 0x106af3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x106af3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106af3 6 (.base 3 (.d8 0x1c)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106af3 6 (.base 3 (.d8 0x1c))).toInstrSpec (mov_m64_r64_effect_step 0x106af3 0x48 (by decide) 6 (.base 3 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x106af7 [0x48, 0x8B, 0x74, 0x24, 0x2C] (LoadPre 0x106af7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x106af7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106af7 6 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x106af7 6 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x106af7 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x106afc [0x48, 0x89, 0x73, 0x24] (StorePre 0x106afc 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x106afc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106afc 6 (.base 3 (.d8 0x24)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106afc 6 (.base 3 (.d8 0x24))).toInstrSpec (mov_m64_r64_effect_step 0x106afc 0x48 (by decide) 6 (.base 3 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x106b00 [0x48, 0x8B, 0x74, 0x24, 0x34] (LoadPre 0x106b00 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x106b00 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106b00 6 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x106b00 6 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r64_m64_effect_step 0x106b00 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x106b05 [0x48, 0x89, 0x73, 0x2C] (StorePre 0x106b05 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x106b05 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106b05 6 (.base 3 (.d8 0x2c)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106b05 6 (.base 3 (.d8 0x2c))).toInstrSpec (mov_m64_r64_effect_step 0x106b05 0x48 (by decide) 6 (.base 3 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x106b09 [0x8B, 0x74, 0x24, 0x3C] (LoadPre 0x106b09 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x106b09 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106b09 6 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x106b09 6 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r32_m32_low_effect_step 0x106b09 6 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x106b0d [0x89, 0x73, 0x34] (StorePre 0x106b0d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x106b0d + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106b0d 6 (.base 3 (.d8 0x34)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x106b0d 6 (.base 3 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x106b0d 6 (.base 3 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x106b10 [0x48, 0x8B, 0x74, 0x24, 0x14] (LoadPre 0x106b10 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106b10 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106b10 6 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x106b10 6 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x106b10 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x106b15 [0x48, 0x89, 0x73, 0x0C] (StorePre 0x106b15 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x106b15 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106b15 6 (.base 3 (.d8 0xc)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106b15 6 (.base 3 (.d8 0xc))).toInstrSpec (mov_m64_r64_effect_step 0x106b15 0x48 (by decide) 6 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x106b19 [0x89, 0x0B] (StorePre 0x106b19 2 (fun s => AddrMode.addr (.base 3 .none) s (0x106b19 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x106b19 1 (.base 3 .none))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x106b19 1 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x106b19 1 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x106b1b [0x88, 0x43, 0x04] (StorePre 0x106b1b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106b1b + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x106b1b 3 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x106b1b 3 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m8_r8_effect_step 0x106b1b 0 (by decide) (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x106b1e [0x89, 0x53, 0x08] (StorePre 0x106b1e 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x106b1e + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106b1e 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x106b1e 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x106b1e 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ad5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ad8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106add) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ae1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ae5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 61), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106aea) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 61), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106aee) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106af3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106af7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106afc) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b00) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b05) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b09) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b0d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b10) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 76), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b15) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 76), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b19) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 76), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b1b) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 76), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b1e) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 76), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b21) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l106ad0_1 code

theorem block_l106ad0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106ad0 :=
  Rest.liftedBlock (rest_l106ad0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106ad0 x hx)

theorem rest_l106b26 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106b26 bytes_l106b26) (entryMap (live .l106b26))
      7 0x106b26 bytes_l106b26 b_l106b26 := by
  have f0 : InstrSpec 0x106b26 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x106b26 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x106b26 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x106b26 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x106b26 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x106b26 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x106b2b [0x41, 0x8B, 0x46, 0x1C] (LoadPre 0x106b2b (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x106b2b + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x106b2b 0 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR32M32Effect_footprint 0x106b2b 0 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x106b2b 0x41 (by decide) 0 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106b2f [0xC7, 0x03, 0x01, 0x00, 0x00, 0x00] (StorePre 0x106b2f 6 (fun s => AddrMode.addr (.base 3 .none) s (0x106b2f + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x106b2f 6 (.base 3 .none) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x106b2f 6 (.base 3 .none) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x106b2f (.base 3 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x106b35 [0x89, 0x43, 0x04] (StorePre 0x106b35 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106b35 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106b35 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x106b35 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x106b35 0 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x106b38 [0xC6, 0x43, 0x08, 0x12] (StorePre 0x106b38 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x106b38 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x106b38 (.base 3 (.d8 0x8)) 0x12)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x106b38 (.base 3 (.d8 0x8)) 0x12).toInstrSpec (mov_m8_imm8_effect_step 0x106b38 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide) 0x12) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x106b3c [0x40, 0x88, 0x6B, 0x09] (StorePre 0x106b3c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x9)) s (0x106b3c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106b3c 4 5 (.base 3 (.d8 0x9)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x106b3c 4 5 (.base 3 (.d8 0x9))).toInstrSpec (mov_m8_r8_rex_effect_step 0x106b3c 0x40 (by decide) 5 (.base 3 (.d8 0x9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b2b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b2f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b35) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b38) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b3c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b40) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 60) (jmp_rel32_effect_step 0x106b40 0xffffff0a (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l106b26 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106b26 :=
  Rest.liftedBlock (rest_l106b26 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106b26 x hx)

theorem rest_l106b45 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106b45 bytes_l106b45) (entryMap (live .l106b45))
      3 0x106b45 bytes_l106b45 b_l106b45 := by
  have f0 : InstrSpec 0x106b45 [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106b45) (movR32Imm32Effect 0x106b45 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x106b45 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x106b45 0xbf (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x106b4a [0x48, 0xC7, 0xC2, 0x30, 0x25, 0x20, 0x00] (fun s => s.RIP = 0x106b4a) (movR64Imm32Effect 0x106b4a 2 0x202530)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x106b4a 2 0x202530).toInstrSpec (mov_r64_imm32_effect_step 0x106b4a 0x48 0xc2 (by decide) (by decide) (by decide) 0x202530) pre_rip
  have f2 : InstrSpec 0x106b51 [0xE8, 0x3A, 0x31, 0x02, 0x00] (PushPre 0x106b51 5) (callEffect (fun _ => 0x129c90) 0x106b56)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106b51 0x129c90 0x106b56).toInstrSpec (call_rel32_effect_step 0x106b51 0x2313a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x106b4a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x106b51) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)]) (p' := 0x129c90) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l106b45 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106b45 :=
  Rest.liftedBlock (rest_l106b45 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106b45 x hx)

theorem rest_l106b56 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106b56 bytes_l106b56) (entryMap (live .l106b56))
      1 0x106b56 bytes_l106b56 b_l106b56 := by
  have f0 : InstrSpec 0x106b56 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106b56) (fun _ => nopEffect 0x106b56 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x106b56 10).toInstrSpec (nop_m_effect_step 0x106b56 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b60) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l106b56 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106b56 :=
  Rest.liftedBlock (rest_l106b56 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106b56 x hx)

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

theorem_by block_l106900_eval :
    program.runBlock (dialect code) ⟨.l106900, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10691d_eval :
    program.runBlock (dialect code) ⟨.l10691d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106926_eval :
    program.runBlock (dialect code) ⟨.l106926, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106935_eval :
    program.runBlock (dialect code) ⟨.l106935, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10694a_eval :
    program.runBlock (dialect code) ⟨.l10694a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106958_eval :
    program.runBlock (dialect code) ⟨.l106958, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1069fd_eval :
    program.runBlock (dialect code) ⟨.l1069fd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106a03_eval :
    program.runBlock (dialect code) ⟨.l106a03, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106a14_eval :
    program.runBlock (dialect code) ⟨.l106a14, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106a26_eval :
    program.runBlock (dialect code) ⟨.l106a26, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106a34_eval :
    program.runBlock (dialect code) ⟨.l106a34, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106a4f_eval :
    program.runBlock (dialect code) ⟨.l106a4f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106a73_eval :
    program.runBlock (dialect code) ⟨.l106a73, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106a79_eval :
    program.runBlock (dialect code) ⟨.l106a79, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106a8a_eval :
    program.runBlock (dialect code) ⟨.l106a8a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106a98_eval :
    program.runBlock (dialect code) ⟨.l106a98, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106aa0_eval :
    program.runBlock (dialect code) ⟨.l106aa0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106aa6_eval :
    program.runBlock (dialect code) ⟨.l106aa6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106ab7_eval :
    program.runBlock (dialect code) ⟨.l106ab7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106ac5_eval :
    program.runBlock (dialect code) ⟨.l106ac5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106ad0_eval :
    program.runBlock (dialect code) ⟨.l106ad0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106b26_eval :
    program.runBlock (dialect code) ⟨.l106b26, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106b45_eval :
    program.runBlock (dialect code) ⟨.l106b45, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106b56_eval :
    program.runBlock (dialect code) ⟨.l106b56, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
