import K256.Proofs.Generate.LIR.CallPre
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

theorem rest_l100180 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100180 bytes_l100180) (entryMap (live .l100180))
      2 0x100180 bytes_l100180 b_l100180 := by
  have f0 : InstrSpec 0x100180 [0x80, 0x3F, 0x00] (LoadPre 0x100180 (fun s => AddrMode.addr (.base 7 .none) s (0x100180 + BitVec.ofNat 64 3)) 1) (cmpM8Imm8Effect 0x100180 3 (.base 7 .none) 0x0)
      [.gpr 7] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x100180 3 (.base 7 .none) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x100180 (.base 7 .none) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100183) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x100183 4 0x1a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100180 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100180 :=
  Rest.liftedBlock (rest_l100180 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100180 x hx)

theorem rest_l100185 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100185 bytes_l100185) (entryMap (live .l100185))
      4 0x100185 bytes_l100185 b_l100185 := by
  have f0 : InstrSpec 0x100185 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x100185) (movR64R64Effect 0x100185 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x100185 0 7).toInstrSpec (mov_r64_r64_effect_step 0x100185 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100188 [0x48, 0x8B, 0x7F, 0x08] (LoadPre 0x100188 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x100188 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100188 7 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x100188 7 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x100188 0x48 (by decide) 7 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10018c [0x48, 0x85, 0xFF] (fun s => s.RIP = 0x10018c) (testR64R64Effect 0x10018c 7 7)
      [.gpr 7, .gpr 7] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x10018c 7 7).toInstrSpec (test_r64_r64_effect_step 0x10018c 0x48 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100188) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10018c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10018f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x10018f 4 0xe) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100185 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100185 :=
  Rest.liftedBlock (rest_l100185 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100185 x hx)

theorem rest_l100191 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100191 bytes_l100191) (entryMap (live .l100191))
      4 0x100191 bytes_l100191 b_l100191 := by
  have f0 : InstrSpec 0x100191 [0x48, 0x8B, 0x40, 0x10] (LoadPre 0x100191 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x100191 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100191 0 (.base 0 (.d8 0x10)))
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100191 0 (.base 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x100191 0x48 (by decide) 0 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100195 [0x48, 0x8B, 0x00] (LoadPre 0x100195 (fun s => AddrMode.addr (.base 0 .none) s (0x100195 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100195 0 (.base 0 .none))
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100195 0 (.base 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x100195 0x48 (by decide) 0 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100198 [0x48, 0x85, 0xC0] (fun s => s.RIP = 0x100198) (testR64R64Effect 0x100198 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x100198 0 0).toInstrSpec (test_r64_r64_effect_step 0x100198 0x48 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100195) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100198) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10019b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x10019b 4 0x2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100191 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100191 :=
  Rest.liftedBlock (rest_l100191 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100191 x hx)

theorem rest_l10019d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10019d bytes_l10019d) (entryMap (live .l10019d))
      0 0x10019d bytes_l10019d b_l10019d := by
  exact Rest.cut

theorem block_l10019d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10019d :=
  Rest.liftedBlock (rest_l10019d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10019d x hx)

theorem rest_l10019f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10019f bytes_l10019f) (entryMap (live .l10019f))
      1 0x10019f bytes_l10019f b_l10019f := by
  have f0 : InstrSpec 0x10019f [0xC3] (RetPre 0x10019f) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10019f).toInstrSpec (ret_effect_step 0x10019f) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f0 (by decide) rfl rfl rfl (by decide)

theorem block_l10019f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10019f :=
  Rest.liftedBlock (rest_l10019f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10019f x hx)

theorem rest_l100240 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100240 bytes_l100240) (entryMap (live .l100240))
      2 0x100240 bytes_l100240 b_l100240 := by
  have f0 : InstrSpec 0x100240 [0x80, 0x3F, 0x00] (LoadPre 0x100240 (fun s => AddrMode.addr (.base 7 .none) s (0x100240 + BitVec.ofNat 64 3)) 1) (cmpM8Imm8Effect 0x100240 3 (.base 7 .none) 0x0)
      [.gpr 7] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x100240 3 (.base 7 .none) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x100240 (.base 7 .none) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100243) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x100243 4 0x1a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100240 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100240 :=
  Rest.liftedBlock (rest_l100240 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100240 x hx)

theorem rest_l100245 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100245 bytes_l100245) (entryMap (live .l100245))
      4 0x100245 bytes_l100245 b_l100245 := by
  have f0 : InstrSpec 0x100245 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x100245) (movR64R64Effect 0x100245 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x100245 0 7).toInstrSpec (mov_r64_r64_effect_step 0x100245 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100248 [0x48, 0x8B, 0x7F, 0x08] (LoadPre 0x100248 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x100248 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100248 7 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x100248 7 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x100248 0x48 (by decide) 7 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10024c [0x48, 0x85, 0xFF] (fun s => s.RIP = 0x10024c) (testR64R64Effect 0x10024c 7 7)
      [.gpr 7, .gpr 7] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x10024c 7 7).toInstrSpec (test_r64_r64_effect_step 0x10024c 0x48 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100248) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10024c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10024f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x10024f 4 0xe) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100245 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100245 :=
  Rest.liftedBlock (rest_l100245 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100245 x hx)

theorem rest_l100251 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100251 bytes_l100251) (entryMap (live .l100251))
      4 0x100251 bytes_l100251 b_l100251 := by
  have f0 : InstrSpec 0x100251 [0x48, 0x8B, 0x40, 0x10] (LoadPre 0x100251 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x100251 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100251 0 (.base 0 (.d8 0x10)))
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100251 0 (.base 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x100251 0x48 (by decide) 0 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100255 [0x48, 0x8B, 0x00] (LoadPre 0x100255 (fun s => AddrMode.addr (.base 0 .none) s (0x100255 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100255 0 (.base 0 .none))
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100255 0 (.base 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x100255 0x48 (by decide) 0 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100258 [0x48, 0x85, 0xC0] (fun s => s.RIP = 0x100258) (testR64R64Effect 0x100258 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x100258 0 0).toInstrSpec (test_r64_r64_effect_step 0x100258 0x48 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100255) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100258) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10025b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x10025b 4 0x2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100251 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100251 :=
  Rest.liftedBlock (rest_l100251 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100251 x hx)

theorem rest_l10025d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10025d bytes_l10025d) (entryMap (live .l10025d))
      0 0x10025d bytes_l10025d b_l10025d := by
  exact Rest.cut

theorem block_l10025d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10025d :=
  Rest.liftedBlock (rest_l10025d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10025d x hx)

theorem rest_l10025f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10025f bytes_l10025f) (entryMap (live .l10025f))
      1 0x10025f bytes_l10025f b_l10025f := by
  have f0 : InstrSpec 0x10025f [0xC3] (RetPre 0x10025f) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10025f).toInstrSpec (ret_effect_step 0x10025f) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f0 (by decide) rfl rfl rfl (by decide)

theorem block_l10025f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10025f :=
  Rest.liftedBlock (rest_l10025f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10025f x hx)

theorem rest_l100a20 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100a20 bytes_l100a20) (entryMap (live .l100a20))
      1 0x100a20 bytes_l100a20 b_l100a20 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x100a20 0xfe (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100a20 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100a20 :=
  Rest.liftedBlock (rest_l100a20 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100a20 x hx)

theorem rest_l100a30 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100a30 bytes_l100a30) (entryMap (live .l100a30))
      1 0x100a30 bytes_l100a30 b_l100a30 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x100a30 0xfe (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100a30 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100a30 :=
  Rest.liftedBlock (rest_l100a30 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100a30 x hx)

theorem rest_l103ec0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103ec0 bytes_l103ec0) (entryMap (live .l103ec0))
      10 0x103ec0 bytes_l103ec0 b_l103ec0 := by
  have f0 : InstrSpec 0x103ec0 [0x55] (PushPre 0x103ec0 1) (pushR64Effect 0x103ec0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103ec0 1 5).toInstrSpec (push_r64_effect_step 0x103ec0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x103ec1 [0x41, 0x57] (PushPre 0x103ec1 2) (pushR64Effect 0x103ec1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103ec1 2 15).toInstrSpec (push_r64_rex_effect_step 0x103ec1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x103ec3 [0x41, 0x56] (PushPre 0x103ec3 2) (pushR64Effect 0x103ec3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103ec3 2 14).toInstrSpec (push_r64_rex_effect_step 0x103ec3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x103ec5 [0x41, 0x55] (PushPre 0x103ec5 2) (pushR64Effect 0x103ec5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103ec5 2 13).toInstrSpec (push_r64_rex_effect_step 0x103ec5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x103ec7 [0x41, 0x54] (PushPre 0x103ec7 2) (pushR64Effect 0x103ec7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103ec7 2 12).toInstrSpec (push_r64_rex_effect_step 0x103ec7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x103ec9 [0x53] (PushPre 0x103ec9 1) (pushR64Effect 0x103ec9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103ec9 1 3).toInstrSpec (push_r64_effect_step 0x103ec9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x103eca [0x50] (PushPre 0x103eca 1) (pushR64Effect 0x103eca 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103eca 1 0).toInstrSpec (push_r64_effect_step 0x103eca 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x103ecb [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x103ecb) (movR64R64Effect 0x103ecb 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x103ecb 3 7).toInstrSpec (mov_r64_r64_effect_step 0x103ecb 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x103ece [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x103ece) (testR64R64Effect 0x103ece 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x103ece 2 2).toInstrSpec (test_r64_r64_effect_step 0x103ece 0x48 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ec1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ec3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ec5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ec7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ec9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eca) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ecb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ece) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ed1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 71) (jcc_rel8_effect_step 0x103ed1 4 0x3b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103ec0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103ec0 :=
  Rest.liftedBlock (rest_l103ec0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103ec0 x hx)

theorem rest_l103ed3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103ed3 bytes_l103ed3) (entryMap (live .l103ed3))
      3 0x103ed3 bytes_l103ed3 b_l103ed3 := by
  have f0 : InstrSpec 0x103ed3 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x103ed3) (movR64R64Effect 0x103ed3 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x103ed3 14 2).toInstrSpec (mov_r64_r64_effect_step 0x103ed3 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103ed6 [0x49, 0x89, 0xF4] (fun s => s.RIP = 0x103ed6) (movR64R64Effect 0x103ed6 12 6)
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x103ed6 12 6).toInstrSpec (mov_r64_r64_effect_step 0x103ed6 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103ed9 [0x48, 0x8D, 0x2D, 0x40, 0x69, 0x02, 0x00] (fun s => s.RIP = 0x103ed9) (leaR64Effect 0x103ed9 5 (.rip 0x26940))
      [] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x103ed9 5 (.rip 0x26940)).toInstrSpec (lea_r64_effect_step 0x103ed9 0x48 (by decide) 5 (.rip 0x26940) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ed6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ed9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ee0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l103ed3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103ed3 :=
  Rest.liftedBlock (rest_l103ed3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103ed3 x hx)

theorem rest_l103ee0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103ee0 bytes_l103ee0) (entryMap (live .l103ee0))
      6 0x103ee0 bytes_l103ee0 b_l103ee0 := by
  have f0 : InstrSpec 0x103ee0 [0x49, 0x83, 0xFE, 0x20] (fun s => s.RIP = 0x103ee0) (cmpR64Imm8Effect 0x103ee0 14 0x20)
      [.gpr 14] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x103ee0 14 0x20).toInstrSpec (cmp_r64_imm8_effect_step 0x103ee0 0x49 0xfe 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103ee4 [0x41, 0xBD, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103ee4) (movR32Imm32Effect 0x103ee4 6 13 0x20)
      [] [] [.reg 13, .rip] :=
    (movR32Imm32Effect_footprint 0x103ee4 6 13 0x20).toInstrSpec (mov_r32_imm32_rex_effect_step 0x103ee4 0x41 0xbd (by decide) (by decide) 0x20) pre_rip
  have f2 : InstrSpec 0x103eea [0x4D, 0x0F, 0x42, 0xEE] (fun s => s.RIP = 0x103eea) (atFlags (condHolds 2) (cmovR64R64Effect 0x103eea 4 13 14))
      [.gpr 13, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 13, .rip] :=
    (cmovR64R64Effect_footprint 0x103eea 4 13 14 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x103eea 2 0x4d (by decide) 0xee (by decide) c)) pre_rip
  have f3 : InstrSpec 0x103eee [0x4F, 0x8D, 0x3C, 0x2C] (fun s => s.RIP = 0x103eee) (leaR64Effect 0x103eee 15 (.sib 12 (some 13) 0 .none))
      [.gpr 12, .gpr 13] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x103eee 15 (.sib 12 (some 13) 0 .none)).toInstrSpec (lea_r64_effect_step 0x103eee 0x4f (by decide) 7 (.sib 12 (some 13) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103ef2 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x103ef2) (movR64R64Effect 0x103ef2 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103ef2 7 3).toInstrSpec (mov_r64_r64_effect_step 0x103ef2 0x48 0xdf (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103ef5 [0xE8, 0x76, 0x0A, 0x00, 0x00] (PushPre 0x103ef5 5) (callEffect (fun _ => 0x104970) 0x103efa)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103ef5 0x104970 0x103efa).toInstrSpec (call_rel32_effect_step 0x103ef5 0xa76 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ee4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eea) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eee) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 59), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ef2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 59), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ef5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 59), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104970) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l103ee0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103ee0 :=
  Rest.liftedBlock (rest_l103ee0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103ee0 x hx)

theorem rest_l103efa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103efa bytes_l103efa) (entryMap (live .l103efa))
      4 0x103efa bytes_l103efa b_l103efa := by
  have f0 : InstrSpec 0x103efa [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x103efa) (movR64R64Effect 0x103efa 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103efa 7 12).toInstrSpec (mov_r64_r64_effect_step 0x103efa 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103efd [0x48, 0x8D, 0x73, 0x20] (fun s => s.RIP = 0x103efd) (leaR64Effect 0x103efd 6 (.base 3 (.d8 0x20)))
      [.gpr 3] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x103efd 6 (.base 3 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x103efd 0x48 (by decide) 6 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103f01 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x103f01) (movR64R64Effect 0x103f01 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x103f01 2 13).toInstrSpec (mov_r64_r64_effect_step 0x103f01 0x4c 0xea (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103f04 [0xFF, 0xD5] (GoesTo (CallPre 0x103f04 2 (fun s => (Operand.reg 5 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x103f06) 0x12a820) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x103f06)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x103f04 5 0x103f06).toInstrSpec (call_r64_effect_step 0x103f04 0xd5 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 5 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103efd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f01) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f04) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l103efa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103efa :=
  Rest.liftedBlock (rest_l103efa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103efa x hx)

theorem rest_l103f06 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103f06 bytes_l103f06) (entryMap (live .l103f06))
      3 0x103f06 bytes_l103f06 b_l103f06 := by
  have f0 : InstrSpec 0x103f06 [0x4D, 0x89, 0xFC] (fun s => s.RIP = 0x103f06) (movR64R64Effect 0x103f06 12 15)
      [.gpr 15] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x103f06 12 15).toInstrSpec (mov_r64_r64_effect_step 0x103f06 0x4d 0xfc (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103f09 [0x4D, 0x29, 0xEE] (fun s => s.RIP = 0x103f09) (subR64R64Effect 0x103f09 14 13)
      [.gpr 14, .gpr 13] [] [.reg 14, .flags, .rip] :=
    (subR64R64Effect_footprint 0x103f09 14 13).toInstrSpec (sub_r64_r64_effect_step 0x103f09 0x4d 0xee (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f09) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 55), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f0c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x103f0c 5 0xd2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103f06 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103f06 :=
  Rest.liftedBlock (rest_l103f06 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103f06 x hx)

theorem rest_l103f0e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103f0e bytes_l103f0e) (entryMap (live .l103f0e))
      11 0x103f0e bytes_l103f0e b_l103f0e := by
  have f0 : InstrSpec 0x103f0e [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103f0e) (movR32Imm32Effect 0x103f0e 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x103f0e 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x103f0e 0xbe (by decide) 0x8) pre_rip
  have f1 : InstrSpec 0x103f13 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x103f13) (movR64R64Effect 0x103f13 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103f13 7 3).toInstrSpec (mov_r64_r64_effect_step 0x103f13 0x48 0xdf (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103f16 [0x31, 0xD2] (fun s => s.RIP = 0x103f16) (xorR32R32Effect 0x103f16 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103f16 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x103f16 0xd2 (by decide)) pre_rip
  have f3 : InstrSpec 0x103f18 [0x48, 0x83, 0xC4, 0x08] (fun s => s.RIP = 0x103f18) (addR64Imm8Effect 0x103f18 4 0x8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x103f18 4 0x8).toInstrSpec (add_r64_imm8_effect_step 0x103f18 0x48 0xc4 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103f1c [0x5B] (PopPre 0x103f1c) (popR64Effect 0x103f1c 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103f1c 1 3).toInstrSpec (pop_r64_effect_step 0x103f1c 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x103f1d [0x41, 0x5C] (PopPre 0x103f1d) (popR64Effect 0x103f1d 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103f1d 2 12).toInstrSpec (pop_r64_rex_effect_step 0x103f1d 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x103f1f [0x41, 0x5D] (PopPre 0x103f1f) (popR64Effect 0x103f1f 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103f1f 2 13).toInstrSpec (pop_r64_rex_effect_step 0x103f1f 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x103f21 [0x41, 0x5E] (PopPre 0x103f21) (popR64Effect 0x103f21 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103f21 2 14).toInstrSpec (pop_r64_rex_effect_step 0x103f21 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x103f23 [0x41, 0x5F] (PopPre 0x103f23) (popR64Effect 0x103f23 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103f23 2 15).toInstrSpec (pop_r64_rex_effect_step 0x103f23 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x103f25 [0x5D] (PopPre 0x103f25) (popR64Effect 0x103f25 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103f25 1 5).toInstrSpec (pop_r64_effect_step 0x103f25 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f13) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f16) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f18) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f1c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(2, 57), (3, 61), (4, 62), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f1d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(2, 57), (3, 61), (4, 65), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f1f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(2, 57), (3, 61), (4, 68), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (13, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f21) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(2, 57), (3, 61), (4, 71), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (13, 67), (14, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f23) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(2, 57), (3, 61), (4, 74), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (13, 67), (14, 70), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f25) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f9 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(2, 57), (3, 61), (4, 77), (5, 76), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (13, 67), (14, 70), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f26) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 79) (jmp_rel32_effect_step 0x103f26 0x5 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103f0e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103f0e :=
  Rest.liftedBlock (rest_l103f0e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103f0e x hx)

theorem rest_l1067b0_2 [Bindings] (code : CodeMap) :
    Rest (n := 128) code lifted (codeRange 0x1067b0 bytes_l1067b0) [(0, 71), (1, 126), (2, 94), (3, 115), (4, 55), (5, 5), (6, 123), (7, 7), (8, 119), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      10 0x106841 bytes_l1067b0_2 b_l1067b0_2 := by
  have f40 : InstrSpec 0x106841 [0xF7, 0xD9] (fun s => s.RIP = 0x106841) (negR32Effect 0x106841 2 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR32Effect_footprint 0x106841 2 1).toInstrSpec (neg_r32_effect_step 0x106841 0xd9 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x106843 [0x21, 0xF1] (fun s => s.RIP = 0x106843) (andR32R32Effect 0x106843 2 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (andR32R32Effect_footprint 0x106843 2 1 6).toInstrSpec (and_r32_r32_effect_step 0x106843 0xf1 (by decide)) pre_rip
  have f42 : InstrSpec 0x106845 [0x01, 0xC2] (fun s => s.RIP = 0x106845) (addR32R32Effect 0x106845 2 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (addR32R32Effect_footprint 0x106845 2 2 0).toInstrSpec (add_r32_r32_effect_step 0x106845 0xc2 (by decide)) pre_rip
  have f43 : InstrSpec 0x106847 [0x01, 0xDA] (fun s => s.RIP = 0x106847) (addR32R32Effect 0x106847 2 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (addR32R32Effect_footprint 0x106847 2 2 3).toInstrSpec (add_r32_r32_effect_step 0x106847 0xda (by decide)) pre_rip
  have f44 : InstrSpec 0x106849 [0x01, 0xCA] (fun s => s.RIP = 0x106849) (addR32R32Effect 0x106849 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (addR32R32Effect_footprint 0x106849 2 2 1).toInstrSpec (add_r32_r32_effect_step 0x106849 0xca (by decide)) pre_rip
  have f45 : InstrSpec 0x10684b [0xB8, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10684b) (movR32Imm32Effect 0x10684b 5 0 0x100)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x10684b 5 0 0x100).toInstrSpec (mov_r32_imm32_effect_step 0x10684b 0xb8 (by decide) 0x100) pre_rip
  have f46 : InstrSpec 0x106850 [0x29, 0xD0] (fun s => s.RIP = 0x106850) (subR32R32Effect 0x106850 2 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (subR32R32Effect_footprint 0x106850 2 0 2).toInstrSpec (sub_r32_r32_effect_step 0x106850 0xd0 (by decide)) pre_rip
  have f47 : InstrSpec 0x106852 [0x48, 0x83, 0xC4, 0x01] (fun s => s.RIP = 0x106852) (addR64Imm8Effect 0x106852 4 0x1)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x106852 4 0x1).toInstrSpec (add_r64_imm8_effect_step 0x106852 0x48 0xc4 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x106856 [0x5B] (PopPre 0x106856) (popR64Effect 0x106856 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106856 1 3).toInstrSpec (pop_r64_effect_step 0x106856 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f49 : InstrSpec 0x106857 [0xC3] (RetPre 0x106857) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x106857).toInstrSpec (ret_effect_step 0x106857) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f40 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 71), (1, 128), (2, 94), (3, 115), (4, 55), (5, 5), (6, 123), (7, 7), (8, 119), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106843) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f41 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 71), (1, 130), (2, 94), (3, 115), (4, 55), (5, 5), (6, 123), (7, 7), (8, 119), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106845) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f42 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 71), (1, 130), (2, 132), (3, 115), (4, 55), (5, 5), (6, 123), (7, 7), (8, 119), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106847) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f43 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 71), (1, 130), (2, 134), (3, 115), (4, 55), (5, 5), (6, 123), (7, 7), (8, 119), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106849) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f44 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 71), (1, 130), (2, 136), (3, 115), (4, 55), (5, 5), (6, 123), (7, 7), (8, 119), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10684b) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f45 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 138), (1, 130), (2, 136), (3, 115), (4, 55), (5, 5), (6, 123), (7, 7), (8, 119), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106850) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f46 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 140), (1, 130), (2, 136), (3, 115), (4, 55), (5, 5), (6, 123), (7, 7), (8, 119), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106852) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f47 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 140), (1, 130), (2, 136), (3, 115), (4, 142), (5, 5), (6, 123), (7, 7), (8, 119), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106856) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f48 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 145) f48 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 146) (ρ' := [(0, 140), (1, 130), (2, 136), (3, 144), (4, 145), (5, 5), (6, 123), (7, 7), (8, 119), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106857) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f49 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 148) f49 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 149) (ρ' := [(0, 140), (1, 130), (2, 136), (3, 144), (4, 148), (5, 5), (6, 123), (7, 7), (8, 119), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f49 (by decide) rfl rfl rfl (by decide)

theorem rest_l1067b0_1 [Bindings] (code : CodeMap) :
    Rest (n := 90) code lifted (codeRange 0x1067b0 bytes_l1067b0) [(0, 71), (2, 57), (3, 3), (4, 55), (5, 5), (6, 86), (7, 7), (8, 88), (9, 73), (10, 79), (12, 12), (13, 13), (14, 14), (15, 15), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]
      30 0x1067f9 bytes_l1067b0_1 b_l1067b0_1 := by
  have f20 : InstrSpec 0x1067f9 [0x0F, 0xB6, 0x14, 0x24] (LoadPre 0x1067f9 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1067f9 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1067f9 4 2 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1067f9 4 2 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x1067f9 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x1067fd [0xF7, 0xDA] (fun s => s.RIP = 0x1067fd) (negR32Effect 0x1067fd 2 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR32Effect_footprint 0x1067fd 2 2).toInstrSpec (neg_r32_effect_step 0x1067fd 0xda (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x1067ff [0x44, 0x21, 0xD2] (fun s => s.RIP = 0x1067ff) (andR32R32Effect 0x1067ff 3 2 10)
      [.gpr 2, .gpr 10] [] [.reg 2, .flags, .rip] :=
    (andR32R32Effect_footprint 0x1067ff 3 2 10).toInstrSpec (and_r32_r32_rex_effect_step 0x1067ff 0x44 0xd2 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x106802 [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x106802) (xorR32R32Effect 0x106802 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106802 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x106802 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x106805 [0x4D, 0x85, 0xC9] (fun s => s.RIP = 0x106805) (testR64R64Effect 0x106805 9 9)
      [.gpr 9, .gpr 9] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x106805 9 9).toInstrSpec (test_r64_r64_effect_step 0x106805 0x4d 0xc9 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x106808 [0x45, 0x0F, 0x45, 0xC2] (fun s => s.RIP = 0x106808) (atFlags (condHolds 5) (cmovR32R32Effect 0x106808 4 8 10))
      [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 8, .rip] :=
    (cmovR32R32Effect_footprint 0x106808 4 8 10 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_rex_effect_step 0x106808 5 0x45 (by decide) 0xc2 (by decide) c)) pre_rip
  have f26 : InstrSpec 0x10680c [0x4C, 0x8B, 0x4F, 0x08] (LoadPre 0x10680c (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10680c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10680c 9 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x10680c 9 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10680c 0x4c (by decide) 1 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x106810 [0x41, 0xBB, 0x7F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106810) (movR32Imm32Effect 0x106810 6 11 0x7f)
      [] [] [.reg 11, .rip] :=
    (movR32Imm32Effect_footprint 0x106810 6 11 0x7f).toInstrSpec (mov_r32_imm32_rex_effect_step 0x106810 0x41 0xbb (by decide) (by decide) 0x7f) pre_rip
  have f28 : InstrSpec 0x106816 [0x4D, 0x0F, 0xBD, 0xD9] (fun s => s.RIP = 0x106816) (bsrR64R64Effect 0x106816 4 11 9)
      [.gpr 11, .gpr 9] [] [.reg 11, .flags, .rip] :=
    (bsrR64R64Effect_footprint 0x106816 4 11 9).toInstrSpec (bsr_r64_r64_effect_step 0x106816 0x4d (by decide) 0xd9 (by decide)) pre_rip
  have f29 : InstrSpec 0x10681a [0x41, 0x83, 0xF3, 0x3F] (fun s => s.RIP = 0x10681a) (xorR32Imm8Effect 0x10681a 4 11 0x3f)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x10681a 4 11 0x3f).toInstrSpec (xor_r32_imm8_rex_effect_step 0x10681a 0x41 0xf3 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10681e [0x44, 0x88, 0x04, 0x24] (StorePre 0x10681e 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10681e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10681e 4 8 (.sib 4 none 0 .none))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10681e 4 8 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x10681e 0x44 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x106822 [0x0F, 0xB6, 0x1C, 0x24] (LoadPre 0x106822 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106822 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x106822 4 3 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x106822 4 3 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x106822 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x106826 [0xF7, 0xDB] (fun s => s.RIP = 0x106826) (negR32Effect 0x106826 2 3)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (negR32Effect_footprint 0x106826 2 3).toInstrSpec (neg_r32_effect_step 0x106826 0xdb (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x106828 [0x44, 0x21, 0xDB] (fun s => s.RIP = 0x106828) (andR32R32Effect 0x106828 3 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (andR32R32Effect_footprint 0x106828 3 3 11).toInstrSpec (and_r32_r32_rex_effect_step 0x106828 0x44 0xdb (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x10682b [0x4D, 0x85, 0xC9] (fun s => s.RIP = 0x10682b) (testR64R64Effect 0x10682b 9 9)
      [.gpr 9, .gpr 9] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x10682b 9 9).toInstrSpec (test_r64_r64_effect_step 0x10682b 0x4d 0xc9 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x10682e [0x45, 0x0F, 0x45, 0xC2] (fun s => s.RIP = 0x10682e) (atFlags (condHolds 5) (cmovR32R32Effect 0x10682e 4 8 10))
      [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 8, .rip] :=
    (cmovR32R32Effect_footprint 0x10682e 4 8 10 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_rex_effect_step 0x10682e 5 0x45 (by decide) 0xc2 (by decide) c)) pre_rip
  have f36 : InstrSpec 0x106832 [0x48, 0x0F, 0xBD, 0x37] (LoadPre 0x106832 (fun s => AddrMode.addr (.base 7 .none) s (0x106832 + BitVec.ofNat 64 4)) 8) (bsrR64M64Effect 0x106832 4 6 (.base 7 .none))
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (bsrR64M64Effect_footprint 0x106832 4 6 (.base 7 .none)).toInstrSpec (bsr_r64_m64_effect_step 0x106832 0x48 (by decide) 6 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x106836 [0x83, 0xF6, 0x3F] (fun s => s.RIP = 0x106836) (xorR32Imm8Effect 0x106836 3 6 0x3f)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x106836 3 6 0x3f).toInstrSpec (xor_r32_imm8_effect_step 0x106836 0xf6 0x3f (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x106839 [0x44, 0x88, 0x04, 0x24] (StorePre 0x106839 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106839 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106839 4 8 (.sib 4 none 0 .none))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x106839 4 8 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x106839 0x44 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x10683d [0x0F, 0xB6, 0x0C, 0x24] (LoadPre 0x10683d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10683d + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10683d 4 1 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10683d 4 1 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x10683d 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 71), (2, 90), (3, 3), (4, 55), (5, 5), (6, 86), (7, 7), (8, 88), (9, 73), (10, 79), (12, 12), (13, 13), (14, 14), (15, 15), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067fd) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f21 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 71), (2, 92), (3, 3), (4, 55), (5, 5), (6, 86), (7, 7), (8, 88), (9, 73), (10, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067ff) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 71), (2, 94), (3, 3), (4, 55), (5, 5), (6, 86), (7, 7), (8, 88), (9, 73), (10, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106802) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f23 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 71), (2, 94), (3, 3), (4, 55), (5, 5), (6, 86), (7, 7), (8, 88), (9, 73), (10, 96), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106805) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f24 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 71), (2, 94), (3, 3), (4, 55), (5, 5), (6, 86), (7, 7), (8, 88), (9, 73), (10, 96), (12, 12), (13, 13), (14, 14), (15, 15), (19, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106808) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f25 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 71), (2, 94), (3, 3), (4, 55), (5, 5), (6, 86), (7, 7), (8, 100), (9, 73), (10, 96), (12, 12), (13, 13), (14, 14), (15, 15), (19, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10680c) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f26 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 71), (2, 94), (3, 3), (4, 55), (5, 5), (6, 86), (7, 7), (8, 100), (9, 102), (10, 96), (12, 12), (13, 13), (14, 14), (15, 15), (19, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106810) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f27 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 71), (2, 94), (3, 3), (4, 55), (5, 5), (6, 86), (7, 7), (8, 100), (9, 102), (10, 96), (11, 104), (12, 12), (13, 13), (14, 14), (15, 15), (19, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106816) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f28 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 71), (2, 94), (3, 3), (4, 55), (5, 5), (6, 86), (7, 7), (8, 100), (9, 102), (10, 96), (11, 106), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10681a) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f29 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 71), (2, 94), (3, 3), (4, 55), (5, 5), (6, 86), (7, 7), (8, 100), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10681e) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.exec (n := 110) (ρ' := [(0, 71), (2, 94), (3, 3), (4, 55), (5, 5), (6, 86), (7, 7), (8, 100), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106822) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f31 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 71), (2, 94), (3, 111), (4, 55), (5, 5), (6, 86), (7, 7), (8, 100), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106826) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f32 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 71), (2, 94), (3, 113), (4, 55), (5, 5), (6, 86), (7, 7), (8, 100), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106828) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f33 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 71), (2, 94), (3, 115), (4, 55), (5, 5), (6, 86), (7, 7), (8, 100), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10682b) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f34 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 71), (2, 94), (3, 115), (4, 55), (5, 5), (6, 86), (7, 7), (8, 100), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (19, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10682e) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f35 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 71), (2, 94), (3, 115), (4, 55), (5, 5), (6, 86), (7, 7), (8, 119), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (19, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106832) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 71), (2, 94), (3, 115), (4, 55), (5, 5), (6, 121), (7, 7), (8, 119), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106836) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 71), (2, 94), (3, 115), (4, 55), (5, 5), (6, 123), (7, 7), (8, 119), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106839) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.exec (n := 125) (ρ' := [(0, 71), (2, 94), (3, 115), (4, 55), (5, 5), (6, 123), (7, 7), (8, 119), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10683d) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f39 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 71), (1, 126), (2, 94), (3, 115), (4, 55), (5, 5), (6, 123), (7, 7), (8, 119), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106841) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1067b0_2 code

theorem rest_l1067b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1067b0 bytes_l1067b0) (entryMap (live .l1067b0))
      50 0x1067b0 bytes_l1067b0 b_l1067b0 := by
  have f0 : InstrSpec 0x1067b0 [0x53] (PushPre 0x1067b0 1) (pushR64Effect 0x1067b0 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1067b0 1 3).toInstrSpec (push_r64_effect_step 0x1067b0 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1067b1 [0x48, 0x83, 0xEC, 0x01] (fun s => s.RIP = 0x1067b1) (subR64Imm8Effect 0x1067b1 4 0x1)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1067b1 4 0x1).toInstrSpec (sub_r64_imm8_effect_step 0x1067b1 0x48 0xec 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1067b5 [0x48, 0x8B, 0x57, 0x18] (LoadPre 0x1067b5 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x1067b5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1067b5 2 (.base 7 (.d8 0x18)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1067b5 2 (.base 7 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1067b5 0x48 (by decide) 2 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1067b9 [0xBE, 0x7F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1067b9) (movR32Imm32Effect 0x1067b9 5 6 0x7f)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1067b9 5 6 0x7f).toInstrSpec (mov_r32_imm32_effect_step 0x1067b9 0xbe (by decide) 0x7f) pre_rip
  have f4 : InstrSpec 0x1067be [0x48, 0x0F, 0xBD, 0xF2] (fun s => s.RIP = 0x1067be) (bsrR64R64Effect 0x1067be 4 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (bsrR64R64Effect_footprint 0x1067be 4 6 2).toInstrSpec (bsr_r64_r64_effect_step 0x1067be 0x48 (by decide) 0xf2 (by decide)) pre_rip
  have f5 : InstrSpec 0x1067c2 [0x83, 0xF6, 0x3F] (fun s => s.RIP = 0x1067c2) (xorR32Imm8Effect 0x1067c2 3 6 0x3f)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x1067c2 3 6 0x3f).toInstrSpec (xor_r32_imm8_effect_step 0x1067c2 0xf6 0x3f (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1067c5 [0xC6, 0x04, 0x24, 0x01] (StorePre 0x1067c5 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1067c5 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1067c5 (.sib 4 none 0 .none) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1067c5 (.sib 4 none 0 .none) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x1067c5 (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1067c9 [0x48, 0x89, 0xE1] (fun s => s.RIP = 0x1067c9) (movR64R64Effect 0x1067c9 1 4)
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1067c9 1 4).toInstrSpec (mov_r64_r64_effect_step 0x1067c9 0x48 0xe1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1067cc [0x0F, 0xB6, 0x04, 0x24] (LoadPre 0x1067cc (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1067cc + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1067cc 4 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1067cc 4 0 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x1067cc 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1067d0 [0xF7, 0xD8] (fun s => s.RIP = 0x1067d0) (negR32Effect 0x1067d0 2 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR32Effect_footprint 0x1067d0 2 0).toInstrSpec (neg_r32_effect_step 0x1067d0 0xd8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1067d2 [0x21, 0xF0] (fun s => s.RIP = 0x1067d2) (andR32R32Effect 0x1067d2 2 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (andR32R32Effect_footprint 0x1067d2 2 0 6).toInstrSpec (and_r32_r32_effect_step 0x1067d2 0xf0 (by decide)) pre_rip
  have f11 : InstrSpec 0x1067d4 [0x4C, 0x8B, 0x4F, 0x10] (LoadPre 0x1067d4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x1067d4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1067d4 9 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1067d4 9 (.base 7 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1067d4 0x4c (by decide) 1 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1067d8 [0x41, 0xBA, 0x7F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1067d8) (movR32Imm32Effect 0x1067d8 6 10 0x7f)
      [] [] [.reg 10, .rip] :=
    (movR32Imm32Effect_footprint 0x1067d8 6 10 0x7f).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1067d8 0x41 0xba (by decide) (by decide) 0x7f) pre_rip
  have f13 : InstrSpec 0x1067de [0x4D, 0x0F, 0xBD, 0xD1] (fun s => s.RIP = 0x1067de) (bsrR64R64Effect 0x1067de 4 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (bsrR64R64Effect_footprint 0x1067de 4 10 9).toInstrSpec (bsr_r64_r64_effect_step 0x1067de 0x4d (by decide) 0xd1 (by decide)) pre_rip
  have f14 : InstrSpec 0x1067e2 [0x41, 0x83, 0xF2, 0x3F] (fun s => s.RIP = 0x1067e2) (xorR32Imm8Effect 0x1067e2 4 10 0x3f)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x1067e2 4 10 0x3f).toInstrSpec (xor_r32_imm8_rex_effect_step 0x1067e2 0x41 0xf2 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1067e6 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x1067e6) (xorR32R32Effect 0x1067e6 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1067e6 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1067e6 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1067e9 [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x1067e9) (testR64R64Effect 0x1067e9 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1067e9 2 2).toInstrSpec (test_r64_r64_effect_step 0x1067e9 0x48 0xd2 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1067ec [0x0F, 0x94, 0x04, 0x24] (StorePre 0x1067ec 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1067ec + BitVec.ofNat 64 4)) 1) (atFlags (condHolds 4) (setccM8Effect 0x1067ec 4 (.sib 4 none 0 .none)))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x1067ec 4 (.sib 4 none 0 .none) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x1067ec 4 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1067f0 [0xBE, 0x7F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1067f0) (movR32Imm32Effect 0x1067f0 5 6 0x7f)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1067f0 5 6 0x7f).toInstrSpec (mov_r32_imm32_effect_step 0x1067f0 0xbe (by decide) 0x7f) pre_rip
  have f19 : InstrSpec 0x1067f5 [0x41, 0x0F, 0x94, 0xC0] (fun s => s.RIP = 0x1067f5) (atFlags (condHolds 4) (setccR8Effect 0x1067f5 4 8))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 8, .rip] :=
    (setccR8Effect_footprint 0x1067f5 4 8 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x1067f5 4 0x41 (by decide) 0xc0 (by decide) c)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067b1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067b5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 55), (5, 5), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067b9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 55), (5, 5), (6, 59), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067be) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 57), (3, 3), (4, 55), (5, 5), (6, 61), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067c2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 57), (3, 3), (4, 55), (5, 5), (6, 63), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067c5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(2, 57), (3, 3), (4, 55), (5, 5), (6, 63), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067c9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(2, 57), (3, 3), (4, 55), (5, 5), (6, 63), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067cc) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (2, 57), (3, 3), (4, 55), (5, 5), (6, 63), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067d0) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (2, 57), (3, 3), (4, 55), (5, 5), (6, 63), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067d2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (2, 57), (3, 3), (4, 55), (5, 5), (6, 63), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067d4) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (2, 57), (3, 3), (4, 55), (5, 5), (6, 63), (7, 7), (8, 8), (9, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067d8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 71), (2, 57), (3, 3), (4, 55), (5, 5), (6, 63), (7, 7), (8, 8), (9, 73), (10, 75), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067de) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (2, 57), (3, 3), (4, 55), (5, 5), (6, 63), (7, 7), (8, 8), (9, 73), (10, 77), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067e2) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 71), (2, 57), (3, 3), (4, 55), (5, 5), (6, 63), (7, 7), (8, 8), (9, 73), (10, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067e6) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 71), (2, 57), (3, 3), (4, 55), (5, 5), (6, 63), (7, 7), (8, 81), (9, 73), (10, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067e9) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 71), (2, 57), (3, 3), (4, 55), (5, 5), (6, 63), (7, 7), (8, 81), (9, 73), (10, 79), (12, 12), (13, 13), (14, 14), (15, 15), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067ec) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 71), (2, 57), (3, 3), (4, 55), (5, 5), (6, 63), (7, 7), (8, 81), (9, 73), (10, 79), (12, 12), (13, 13), (14, 14), (15, 15), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067f0) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 71), (2, 57), (3, 3), (4, 55), (5, 5), (6, 86), (7, 7), (8, 81), (9, 73), (10, 79), (12, 12), (13, 13), (14, 14), (15, 15), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067f5) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 71), (2, 57), (3, 3), (4, 55), (5, 5), (6, 86), (7, 7), (8, 88), (9, 73), (10, 79), (12, 12), (13, 13), (14, 14), (15, 15), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067f9) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1067b0_1 code

theorem block_l1067b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1067b0 :=
  Rest.liftedBlock (rest_l1067b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1067b0 x hx)

theorem rest_l106860 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106860 bytes_l106860) (entryMap (live .l106860))
      6 0x106860 bytes_l106860 b_l106860 := by
  have f0 : InstrSpec 0x106860 [0x53] (PushPre 0x106860 1) (pushR64Effect 0x106860 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106860 1 3).toInstrSpec (push_r64_effect_step 0x106860 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x106861 [0x48, 0x83, 0xEC, 0x40] (fun s => s.RIP = 0x106861) (subR64Imm8Effect 0x106861 4 0x40)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x106861 4 0x40).toInstrSpec (sub_r64_imm8_effect_step 0x106861 0x48 0xec 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106865 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x106865) (movR64R64Effect 0x106865 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x106865 3 7).toInstrSpec (mov_r64_r64_effect_step 0x106865 0x48 0xfb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x106868 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x106868) (leaR64Effect 0x106868 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x106868 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x106868 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10686d [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10686d) (movR32Imm32Effect 0x10686d 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10686d 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x10686d 0xba (by decide) 0x1) pre_rip
  have f5 : InstrSpec 0x106872 [0xE8, 0x09, 0x13, 0x02, 0x00] (PushPre 0x106872 5) (callEffect (fun _ => 0x127b80) 0x106877)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106872 0x127b80 0x106877).toInstrSpec (call_rel32_effect_step 0x106872 0x21309 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106861) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106865) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 57), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106868) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 57), (4, 55), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10686d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 61), (3, 57), (4, 55), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106872) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 61), (3, 57), (4, 63), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l106860 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106860 :=
  Rest.liftedBlock (rest_l106860 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106860 x hx)

theorem rest_l106877 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106877 bytes_l106877) (entryMap (live .l106877))
      3 0x106877 bytes_l106877 b_l106877 := by
  have f0 : InstrSpec 0x106877 [0x8B, 0x44, 0x24, 0x08] (LoadPre 0x106877 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106877 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106877 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x106877 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x106877 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10687b [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x10687b) (cmpR32Imm8Effect 0x10687b 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x10687b 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x10687b 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10687b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10687e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x10687e 5 0x18) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106877 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106877 :=
  Rest.liftedBlock (rest_l106877 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106877 x hx)

theorem rest_l106880 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106880 bytes_l106880) (entryMap (live .l106880))
      3 0x106880 bytes_l106880 b_l106880 := by
  have f0 : InstrSpec 0x106880 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x106880 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x106880 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106880 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x106880 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x106880 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106885 [0x48, 0x83, 0xFE, 0x01] (fun s => s.RIP = 0x106885) (cmpR64Imm8Effect 0x106885 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x106885 6 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x106885 0x48 0xfe 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106885) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106889) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x106889 5 0x55) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106880 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106880 :=
  Rest.liftedBlock (rest_l106880 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106880 x hx)

theorem rest_l10688b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10688b bytes_l10688b) (entryMap (live .l10688b))
      4 0x10688b bytes_l10688b b_l10688b := by
  have f0 : InstrSpec 0x10688b [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x10688b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10688b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10688b 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10688b 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10688b 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106890 [0x0F, 0xB6, 0x09] (LoadPre 0x106890 (fun s => AddrMode.addr (.base 1 .none) s (0x106890 + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x106890 3 1 (.base 1 .none))
      [.gpr 1] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x106890 3 1 (.base 1 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x106890 1 (.base 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106893 [0x88, 0x4B, 0x04] (StorePre 0x106893 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106893 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x106893 3 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x106893 3 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m8_r8_effect_step 0x106893 1 (by decide) (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106890) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106893) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106896) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 58) (jmp_rel8_effect_step 0x106896 0x3d (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10688b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10688b :=
  Rest.liftedBlock (rest_l10688b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10688b x hx)

theorem rest_l106898 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106898 bytes_l106898) (entryMap (live .l106898))
      14 0x106898 bytes_l106898 b_l106898 := by
  have f0 : InstrSpec 0x106898 [0x8B, 0x4C, 0x24, 0x0C] (LoadPre 0x106898 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106898 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106898 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x106898 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x106898 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10689c [0x48, 0x8B, 0x54, 0x24, 0x10] (LoadPre 0x10689c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10689c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10689c 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10689c 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10689c 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1068a1 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x1068a1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1068a1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1068a1 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1068a1 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1068a1 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1068a6 [0x48, 0x8B, 0x7C, 0x24, 0x38] (LoadPre 0x1068a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1068a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1068a6 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1068a6 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1068a6 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1068ab [0x48, 0x89, 0x7B, 0x30] (StorePre 0x1068ab 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x1068ab + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1068ab 7 (.base 3 (.d8 0x30)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1068ab 7 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1068ab 0x48 (by decide) 7 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1068af [0x48, 0x8B, 0x7C, 0x24, 0x30] (LoadPre 0x1068af (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1068af + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1068af 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1068af 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1068af 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1068b4 [0x48, 0x89, 0x7B, 0x28] (StorePre 0x1068b4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1068b4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1068b4 7 (.base 3 (.d8 0x28)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1068b4 7 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1068b4 0x48 (by decide) 7 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1068b8 [0x48, 0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x1068b8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1068b8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1068b8 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1068b8 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1068b8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1068bd [0x48, 0x89, 0x7B, 0x20] (StorePre 0x1068bd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1068bd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1068bd 7 (.base 3 (.d8 0x20)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1068bd 7 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1068bd 0x48 (by decide) 7 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1068c1 [0x48, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x1068c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1068c1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1068c1 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1068c1 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1068c1 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1068c6 [0x48, 0x89, 0x7B, 0x18] (StorePre 0x1068c6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1068c6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1068c6 7 (.base 3 (.d8 0x18)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1068c6 7 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1068c6 0x48 (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1068ca [0x89, 0x4B, 0x04] (StorePre 0x1068ca 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1068ca + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1068ca 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1068ca 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x1068ca 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1068cd [0x48, 0x89, 0x53, 0x08] (StorePre 0x1068cd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1068cd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1068cd 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1068cd 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1068cd 0x48 (by decide) 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1068d1 [0x48, 0x89, 0x73, 0x10] (StorePre 0x1068d1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1068d1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1068d1 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1068d1 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1068d1 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10689c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068a1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068a6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068ab) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068af) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068b4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068b8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068bd) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068c1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068c6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068ca) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068cd) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068d1) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068d5) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 74) (by decide) rfl

theorem block_l106898 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106898 :=
  Rest.liftedBlock (rest_l106898 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106898 x hx)

theorem rest_l1068d5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1068d5 bytes_l1068d5) (entryMap (live .l1068d5))
      5 0x1068d5 bytes_l1068d5 b_l1068d5 := by
  have f0 : InstrSpec 0x1068d5 [0x89, 0x03] (StorePre 0x1068d5 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1068d5 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1068d5 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1068d5 0 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x1068d5 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1068d7 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1068d7) (movR64R64Effect 0x1068d7 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1068d7 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1068d7 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1068da [0x48, 0x83, 0xC4, 0x40] (fun s => s.RIP = 0x1068da) (addR64Imm8Effect 0x1068da 4 0x40)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1068da 4 0x40).toInstrSpec (add_r64_imm8_effect_step 0x1068da 0x48 0xc4 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1068de [0x5B] (PopPre 0x1068de) (popR64Effect 0x1068de 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1068de 1 3).toInstrSpec (pop_r64_effect_step 0x1068de 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1068df [0xC3] (RetPre 0x1068df) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1068df).toInstrSpec (ret_effect_step 0x1068df) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068d7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068da) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068de) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068df) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 63) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l1068d5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1068d5 :=
  Rest.liftedBlock (rest_l1068d5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1068d5 x hx)

theorem rest_l1068e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1068e0 bytes_l1068e0) (entryMap (live .l1068e0))
      3 0x1068e0 bytes_l1068e0 b_l1068e0 := by
  have f0 : InstrSpec 0x1068e0 [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1068e0) (movR32Imm32Effect 0x1068e0 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x1068e0 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1068e0 0xbf (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x1068e5 [0x48, 0xC7, 0xC2, 0x30, 0x25, 0x20, 0x00] (fun s => s.RIP = 0x1068e5) (movR64Imm32Effect 0x1068e5 2 0x202530)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x1068e5 2 0x202530).toInstrSpec (mov_r64_imm32_effect_step 0x1068e5 0x48 0xc2 (by decide) (by decide) (by decide) 0x202530) pre_rip
  have f2 : InstrSpec 0x1068ec [0xE8, 0x9F, 0x33, 0x02, 0x00] (PushPre 0x1068ec 5) (callEffect (fun _ => 0x129c90) 0x1068f1)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1068ec 0x129c90 0x1068f1).toInstrSpec (call_rel32_effect_step 0x1068ec 0x2339f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x1068e5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x1068ec) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)]) (p' := 0x129c90) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l1068e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1068e0 :=
  Rest.liftedBlock (rest_l1068e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1068e0 x hx)

theorem rest_l1068f1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1068f1 bytes_l1068f1) (entryMap (live .l1068f1))
      2 0x1068f1 bytes_l1068f1 b_l1068f1 := by
  have f0 : InstrSpec 0x1068f1 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1068f1) (fun _ => nopEffect 0x1068f1 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1068f1 10).toInstrSpec (nop_m_effect_step 0x1068f1 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1068fb [0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x1068fb) (fun _ => nopEffect 0x1068fb 5)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1068fb 5).toInstrSpec (nop_m_effect_step 0x1068fb [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068fb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106900) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1068f1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1068f1 :=
  Rest.liftedBlock (rest_l1068f1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1068f1 x hx)

theorem rest_l108380 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108380 bytes_l108380) (entryMap (live .l108380))
      14 0x108380 bytes_l108380 b_l108380 := by
  have f0 : InstrSpec 0x108380 [0x53] (PushPre 0x108380 1) (pushR64Effect 0x108380 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108380 1 3).toInstrSpec (push_r64_effect_step 0x108380 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x108381 [0x48, 0x83, 0xEC, 0x50] (fun s => s.RIP = 0x108381) (subR64Imm8Effect 0x108381 4 0x50)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x108381 4 0x50).toInstrSpec (sub_r64_imm8_effect_step 0x108381 0x48 0xec 0x50 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x108385 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x108385) (movR64R64Effect 0x108385 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x108385 3 7).toInstrSpec (mov_r64_r64_effect_step 0x108385 0x48 0xfb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x108388 [0x48, 0xB8, 0x41, 0x41, 0x36, 0xD0, 0x8C, 0x5E, 0xD2, 0xBF] (fun s => s.RIP = 0x108388) (movR64Imm64Effect 0x108388 0 0xbfd25e8cd0364141)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x108388 0 0xbfd25e8cd0364141).toInstrSpec (mov_r64_imm64_effect_step 0x108388 0x48 0xb8 (by decide) (by decide) 0xbfd25e8cd0364141) pre_rip
  have f4 : InstrSpec 0x108392 [0x48, 0x89, 0x44, 0x24, 0x30] (StorePre 0x108392 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108392 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108392 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108392 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x108392 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x108397 [0x48, 0xB8, 0x3B, 0xA0, 0x48, 0xAF, 0xE6, 0xDC, 0xAE, 0xBA] (fun s => s.RIP = 0x108397) (movR64Imm64Effect 0x108397 0 0xbaaedce6af48a03b)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x108397 0 0xbaaedce6af48a03b).toInstrSpec (mov_r64_imm64_effect_step 0x108397 0x48 0xb8 (by decide) (by decide) 0xbaaedce6af48a03b) pre_rip
  have f6 : InstrSpec 0x1083a1 [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x1083a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1083a1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1083a1 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1083a1 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x1083a1 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1083a6 [0x48, 0xC7, 0x44, 0x24, 0x40, 0xFE, 0xFF, 0xFF, 0xFF] (StorePre 0x1083a6 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1083a6 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1083a6 (.sib 4 none 0 (.d8 0x40)) 0xfffffffe)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1083a6 (.sib 4 none 0 (.d8 0x40)) 0xfffffffe).toInstrSpec (mov_m64_imm32_effect_step 0x1083a6 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide) 0xfffffffe) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1083af [0x48, 0xC7, 0x44, 0x24, 0x48, 0xFF, 0xFF, 0xFF, 0xFF] (StorePre 0x1083af 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1083af + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1083af (.sib 4 none 0 (.d8 0x48)) 0xffffffff)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1083af (.sib 4 none 0 (.d8 0x48)) 0xffffffff).toInstrSpec (mov_m64_imm32_effect_step 0x1083af 0x48 (by decide) (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide) 0xffffffff) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1083b8 [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x1083b8) (leaR64Effect 0x1083b8 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1083b8 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1083b8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1083bd [0x48, 0x8D, 0x74, 0x24, 0x30] (fun s => s.RIP = 0x1083bd) (leaR64Effect 0x1083bd 6 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1083bd 6 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x1083bd 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1083c2 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1083c2) (movR32Imm32Effect 0x1083c2 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1083c2 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1083c2 0xba (by decide) 0x1) pre_rip
  have f12 : InstrSpec 0x1083c7 [0x48, 0xC7, 0xC1, 0x68, 0x28, 0x20, 0x00] (fun s => s.RIP = 0x1083c7) (movR64Imm32Effect 0x1083c7 1 0x202868)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x1083c7 1 0x202868).toInstrSpec (mov_r64_imm32_effect_step 0x1083c7 0x48 0xc1 (by decide) (by decide) (by decide) 0x202868) pre_rip
  have f13 : InstrSpec 0x1083ce [0xE8, 0xDD, 0xE1, 0xFF, 0xFF] (PushPre 0x1083ce 5) (callEffect (fun _ => 0x1065b0) 0x1083d3)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1083ce 0x1065b0 0x1083d3).toInstrSpec (call_rel32_effect_step 0x1083ce 0xffffe1dd (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108381) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108385) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 57), (4, 55), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108388) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 57), (4, 55), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108392) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 57), (4, 55), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108397) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 57), (4, 55), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083a1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 57), (4, 55), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083a6) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 62), (3, 57), (4, 55), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083af) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 62), (3, 57), (4, 55), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083b8) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 62), (3, 57), (4, 55), (5, 5), (7, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083bd) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (3, 57), (4, 55), (5, 5), (6, 69), (7, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083c2) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (2, 71), (3, 57), (4, 55), (5, 5), (6, 69), (7, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083c7) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 62), (2, 71), (3, 57), (4, 55), (5, 5), (6, 69), (7, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083ce) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 62), (2, 71), (3, 57), (4, 74), (5, 5), (6, 69), (7, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065b0) f13 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 76) (by decide) (by decide) rfl rfl

theorem block_l108380 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108380 :=
  Rest.liftedBlock (rest_l108380 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108380 x hx)

theorem rest_l1083d3_3 [Bindings] (code : CodeMap) :
    Rest (n := 168) code lifted (codeRange 0x1083d3 bytes_l1083d3) [(0, 166), (1, 147), (2, 161), (3, 3), (4, 4), (5, 5), (6, 141), (7, 153), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x1084a7 bytes_l1083d3_3 b_l1083d3_3 := by
  have f60 : InstrSpec 0x1084a7 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x1084a7) (movzxR32R8Effect 0x1084a7 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x1084a7 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x1084a7 0xf8 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x1084aa [0xE8, 0xA1, 0xF8, 0x01, 0x00] (PushPre 0x1084aa 5) (callEffect (fun _ => 0x127d50) 0x1084af)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1084aa 0x127d50 0x1084af).toInstrSpec (call_rel32_effect_step 0x1084aa 0x1f8a1 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f60 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 166), (1, 147), (2, 161), (3, 3), (4, 4), (5, 5), (6, 141), (7, 168), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084aa) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f61 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 166), (1, 147), (2, 161), (3, 3), (4, 170), (5, 5), (6, 141), (7, 168), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f61 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 172) (by decide) (by decide) rfl rfl

theorem rest_l1083d3_2 [Bindings] (code : CodeMap) :
    Rest (n := 130) code lifted (codeRange 0x1083d3 bytes_l1083d3) [(1, 77), (2, 120), (3, 3), (4, 4), (5, 5), (6, 128), (7, 114), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      22 0x10845e bytes_l1083d3_2 b_l1083d3_2 := by
  have f40 : InstrSpec 0x10845e [0x48, 0x21, 0xD6] (fun s => s.RIP = 0x10845e) (andR64R64Effect 0x10845e 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10845e 6 2).toInstrSpec (and_r64_r64_effect_step 0x10845e 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x108461 [0x4C, 0x09, 0xC6] (fun s => s.RIP = 0x108461) (orR64R64Effect 0x108461 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108461 6 8).toInstrSpec (or_r64_r64_effect_step 0x108461 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x108464 [0x48, 0xC1, 0xEE, 0x3F] (fun s => s.RIP = 0x108464) (shrR64Effect 0x108464 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x108464 4 6 63).toInstrSpec (shr_r64_imm8_effect_step 0x108464 0x48 0xee 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x108468 [0x48, 0x89, 0x74, 0x24, 0x08] (StorePre 0x108468 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108468 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108468 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108468 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x108468 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f44 : InstrSpec 0x10846d [0x48, 0x2B, 0x4C, 0x24, 0x08] (LoadPre 0x10846d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10846d + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10846d 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10846d 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x10846d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f45 : InstrSpec 0x108472 [0x48, 0x8B, 0x54, 0x24, 0x28] (LoadPre 0x108472 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x108472 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108472 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x108472 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x108472 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f46 : InstrSpec 0x108477 [0x48, 0x8B, 0x73, 0x18] (LoadPre 0x108477 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x108477 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108477 6 (.base 3 (.d8 0x18)))
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x108477 6 (.base 3 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x108477 0x48 (by decide) 6 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f47 : InstrSpec 0x10847b [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x10847b) (sarR64Effect 0x10847b 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x10847b 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x10847b 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x10847f [0x48, 0x01, 0xD1] (fun s => s.RIP = 0x10847f) (addR64R64Effect 0x10847f 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10847f 1 2).toInstrSpec (add_r64_r64_effect_step 0x10847f 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x108482 [0x48, 0x29, 0xF1] (fun s => s.RIP = 0x108482) (subR64R64Effect 0x108482 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x108482 1 6).toInstrSpec (sub_r64_r64_effect_step 0x108482 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x108485 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x108485) (notR64Effect 0x108485 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x108485 2).toInstrSpec (not_r64_effect_step 0x108485 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x108488 [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x108488) (movR64R64Effect 0x108488 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x108488 7 6).toInstrSpec (mov_r64_r64_effect_step 0x108488 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x10848b [0x48, 0x21, 0xD7] (fun s => s.RIP = 0x10848b) (andR64R64Effect 0x10848b 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10848b 7 2).toInstrSpec (and_r64_r64_effect_step 0x10848b 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x10848e [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x10848e) (orR64R64Effect 0x10848e 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10848e 2 6).toInstrSpec (or_r64_r64_effect_step 0x10848e 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x108491 [0x48, 0x21, 0xCA] (fun s => s.RIP = 0x108491) (andR64R64Effect 0x108491 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108491 2 1).toInstrSpec (and_r64_r64_effect_step 0x108491 0x48 0xca (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x108494 [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x108494) (orR64R64Effect 0x108494 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108494 2 7).toInstrSpec (or_r64_r64_effect_step 0x108494 0x48 0xfa (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x108497 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x108497) (shrR64Effect 0x108497 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x108497 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x108497 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x10849b [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x10849b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10849b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10849b 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10849b 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10849b 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f58 : InstrSpec 0x1084a0 [0x0F, 0xB6, 0x44, 0x24, 0x08] (LoadPre 0x1084a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1084a0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1084a0 5 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1084a0 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x1084a0 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f59 : InstrSpec 0x1084a5 [0x24, 0x01] (fun s => s.RIP = 0x1084a5) (andAlImm8Effect 0x1084a5 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x1084a5 0x1).toInstrSpec (and_al_imm8_effect_step 0x1084a5 0x1) pre_rip
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f40 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(1, 77), (2, 120), (3, 3), (4, 4), (5, 5), (6, 130), (7, 114), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108461) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f41 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(1, 77), (2, 120), (3, 3), (4, 4), (5, 5), (6, 132), (7, 114), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108464) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f42 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(1, 77), (2, 120), (3, 3), (4, 4), (5, 5), (6, 134), (7, 114), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108468) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.exec (n := 136) (ρ' := [(1, 77), (2, 120), (3, 3), (4, 4), (5, 5), (6, 134), (7, 114), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10846d) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f44 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(1, 137), (2, 120), (3, 3), (4, 4), (5, 5), (6, 134), (7, 114), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108472) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f45 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(1, 137), (2, 139), (3, 3), (4, 4), (5, 5), (6, 134), (7, 114), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108477) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f46 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(1, 137), (2, 139), (3, 3), (4, 4), (5, 5), (6, 141), (7, 114), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10847b) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f47 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(1, 143), (2, 139), (3, 3), (4, 4), (5, 5), (6, 141), (7, 114), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10847f) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f48 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(1, 145), (2, 139), (3, 3), (4, 4), (5, 5), (6, 141), (7, 114), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108482) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f49 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(1, 147), (2, 139), (3, 3), (4, 4), (5, 5), (6, 141), (7, 114), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108485) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f50 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(1, 147), (2, 149), (3, 3), (4, 4), (5, 5), (6, 141), (7, 114), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108488) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f51 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(1, 147), (2, 149), (3, 3), (4, 4), (5, 5), (6, 141), (7, 151), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10848b) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f52 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(1, 147), (2, 149), (3, 3), (4, 4), (5, 5), (6, 141), (7, 153), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10848e) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f53 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(1, 147), (2, 155), (3, 3), (4, 4), (5, 5), (6, 141), (7, 153), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108491) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f54 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(1, 147), (2, 157), (3, 3), (4, 4), (5, 5), (6, 141), (7, 153), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108494) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f55 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(1, 147), (2, 159), (3, 3), (4, 4), (5, 5), (6, 141), (7, 153), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108497) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f56 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(1, 147), (2, 161), (3, 3), (4, 4), (5, 5), (6, 141), (7, 153), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10849b) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.exec (n := 163) (ρ' := [(1, 147), (2, 161), (3, 3), (4, 4), (5, 5), (6, 141), (7, 153), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084a0) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f58 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 164), (1, 147), (2, 161), (3, 3), (4, 4), (5, 5), (6, 141), (7, 153), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084a5) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f59 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 166), (1, 147), (2, 161), (3, 3), (4, 4), (5, 5), (6, 141), (7, 153), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084a7) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1083d3_3 code

theorem rest_l1083d3_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x1083d3 bytes_l1083d3) [(1, 77), (2, 89), (3, 3), (4, 4), (5, 5), (6, 83), (7, 85), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      42 0x10841a bytes_l1083d3_1 b_l1083d3_1 := by
  have f20 : InstrSpec 0x10841a [0x48, 0x29, 0xFA] (fun s => s.RIP = 0x10841a) (subR64R64Effect 0x10841a 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10841a 2 7).toInstrSpec (sub_r64_r64_effect_step 0x10841a 0x48 0xfa (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x10841d [0x48, 0xF7, 0xD6] (fun s => s.RIP = 0x10841d) (notR64Effect 0x10841d 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR64Effect_footprint 0x10841d 6).toInstrSpec (not_r64_effect_step 0x10841d 0x48 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x108420 [0x49, 0x89, 0xF8] (fun s => s.RIP = 0x108420) (movR64R64Effect 0x108420 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x108420 8 7).toInstrSpec (mov_r64_r64_effect_step 0x108420 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x108423 [0x49, 0x21, 0xF0] (fun s => s.RIP = 0x108423) (andR64R64Effect 0x108423 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108423 8 6).toInstrSpec (and_r64_r64_effect_step 0x108423 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x108426 [0x48, 0x09, 0xFE] (fun s => s.RIP = 0x108426) (orR64R64Effect 0x108426 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108426 6 7).toInstrSpec (or_r64_r64_effect_step 0x108426 0x48 0xfe (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x108429 [0x48, 0x21, 0xD6] (fun s => s.RIP = 0x108429) (andR64R64Effect 0x108429 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108429 6 2).toInstrSpec (and_r64_r64_effect_step 0x108429 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10842c [0x4C, 0x09, 0xC6] (fun s => s.RIP = 0x10842c) (orR64R64Effect 0x10842c 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10842c 6 8).toInstrSpec (or_r64_r64_effect_step 0x10842c 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x10842f [0x48, 0xC1, 0xEE, 0x3F] (fun s => s.RIP = 0x10842f) (shrR64Effect 0x10842f 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x10842f 4 6 63).toInstrSpec (shr_r64_imm8_effect_step 0x10842f 0x48 0xee 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x108433 [0x48, 0x89, 0x74, 0x24, 0x08] (StorePre 0x108433 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108433 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108433 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108433 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x108433 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x108438 [0x31, 0xD2] (fun s => s.RIP = 0x108438) (xorR32R32Effect 0x108438 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x108438 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x108438 0xd2 (by decide)) pre_rip
  have f30 : InstrSpec 0x10843a [0x48, 0x2B, 0x54, 0x24, 0x08] (LoadPre 0x10843a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10843a + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10843a 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10843a 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x10843a 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x10843f [0x48, 0x8B, 0x74, 0x24, 0x20] (LoadPre 0x10843f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10843f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10843f 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10843f 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10843f 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x108444 [0x48, 0x8B, 0x7B, 0x10] (LoadPre 0x108444 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x108444 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108444 7 (.base 3 (.d8 0x10)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x108444 7 (.base 3 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x108444 0x48 (by decide) 7 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x108448 [0x48, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x108448) (sarR64Effect 0x108448 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (sarR64Effect_footprint 0x108448 4 2 63).toInstrSpec (sar_r64_imm8_effect_step 0x108448 0x48 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x10844c [0x48, 0x01, 0xF2] (fun s => s.RIP = 0x10844c) (addR64R64Effect 0x10844c 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10844c 2 6).toInstrSpec (add_r64_r64_effect_step 0x10844c 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x10844f [0x48, 0x29, 0xFA] (fun s => s.RIP = 0x10844f) (subR64R64Effect 0x10844f 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10844f 2 7).toInstrSpec (sub_r64_r64_effect_step 0x10844f 0x48 0xfa (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x108452 [0x48, 0xF7, 0xD6] (fun s => s.RIP = 0x108452) (notR64Effect 0x108452 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR64Effect_footprint 0x108452 6).toInstrSpec (not_r64_effect_step 0x108452 0x48 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x108455 [0x49, 0x89, 0xF8] (fun s => s.RIP = 0x108455) (movR64R64Effect 0x108455 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x108455 8 7).toInstrSpec (mov_r64_r64_effect_step 0x108455 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x108458 [0x49, 0x21, 0xF0] (fun s => s.RIP = 0x108458) (andR64R64Effect 0x108458 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108458 8 6).toInstrSpec (and_r64_r64_effect_step 0x108458 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10845b [0x48, 0x09, 0xFE] (fun s => s.RIP = 0x10845b) (orR64R64Effect 0x10845b 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10845b 6 7).toInstrSpec (or_r64_r64_effect_step 0x10845b 0x48 0xfe (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(1, 77), (2, 91), (3, 3), (4, 4), (5, 5), (6, 83), (7, 85), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10841d) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(1, 77), (2, 91), (3, 3), (4, 4), (5, 5), (6, 93), (7, 85), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108420) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(1, 77), (2, 91), (3, 3), (4, 4), (5, 5), (6, 93), (7, 85), (8, 95), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108423) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(1, 77), (2, 91), (3, 3), (4, 4), (5, 5), (6, 93), (7, 85), (8, 97), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108426) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(1, 77), (2, 91), (3, 3), (4, 4), (5, 5), (6, 99), (7, 85), (8, 97), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108429) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f25 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(1, 77), (2, 91), (3, 3), (4, 4), (5, 5), (6, 101), (7, 85), (8, 97), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10842c) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(1, 77), (2, 91), (3, 3), (4, 4), (5, 5), (6, 103), (7, 85), (8, 97), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10842f) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(1, 77), (2, 91), (3, 3), (4, 4), (5, 5), (6, 105), (7, 85), (8, 97), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108433) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(1, 77), (2, 91), (3, 3), (4, 4), (5, 5), (6, 105), (7, 85), (8, 97), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108438) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f29 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(1, 77), (2, 108), (3, 3), (4, 4), (5, 5), (6, 105), (7, 85), (8, 97), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10843a) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f30 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(1, 77), (2, 110), (3, 3), (4, 4), (5, 5), (6, 105), (7, 85), (8, 97), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10843f) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f31 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(1, 77), (2, 110), (3, 3), (4, 4), (5, 5), (6, 112), (7, 85), (8, 97), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108444) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f32 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(1, 77), (2, 110), (3, 3), (4, 4), (5, 5), (6, 112), (7, 114), (8, 97), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108448) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f33 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(1, 77), (2, 116), (3, 3), (4, 4), (5, 5), (6, 112), (7, 114), (8, 97), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10844c) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f34 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(1, 77), (2, 118), (3, 3), (4, 4), (5, 5), (6, 112), (7, 114), (8, 97), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10844f) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f35 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(1, 77), (2, 120), (3, 3), (4, 4), (5, 5), (6, 112), (7, 114), (8, 97), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108452) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f36 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(1, 77), (2, 120), (3, 3), (4, 4), (5, 5), (6, 122), (7, 114), (8, 97), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108455) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f37 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(1, 77), (2, 120), (3, 3), (4, 4), (5, 5), (6, 122), (7, 114), (8, 124), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108458) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f38 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(1, 77), (2, 120), (3, 3), (4, 4), (5, 5), (6, 122), (7, 114), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10845b) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f39 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(1, 77), (2, 120), (3, 3), (4, 4), (5, 5), (6, 128), (7, 114), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10845e) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1083d3_2 code

theorem rest_l1083d3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1083d3 bytes_l1083d3) (entryMap (live .l1083d3))
      62 0x1083d3 bytes_l1083d3 b_l1083d3 := by
  have f0 : InstrSpec 0x1083d3 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1083d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1083d3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1083d3 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1083d3 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1083d3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1083d8 [0x48, 0x8B, 0x0B] (LoadPre 0x1083d8 (fun s => AddrMode.addr (.base 3 .none) s (0x1083d8 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1083d8 1 (.base 3 .none))
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1083d8 1 (.base 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1083d8 0x48 (by decide) 1 (.base 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1083db [0x48, 0x89, 0xC2] (fun s => s.RIP = 0x1083db) (movR64R64Effect 0x1083db 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1083db 2 0).toInstrSpec (mov_r64_r64_effect_step 0x1083db 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1083de [0x48, 0x29, 0xCA] (fun s => s.RIP = 0x1083de) (subR64R64Effect 0x1083de 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1083de 2 1).toInstrSpec (sub_r64_r64_effect_step 0x1083de 0x48 0xca (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1083e1 [0x48, 0xF7, 0xD0] (fun s => s.RIP = 0x1083e1) (notR64Effect 0x1083e1 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR64Effect_footprint 0x1083e1 0).toInstrSpec (not_r64_effect_step 0x1083e1 0x48 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1083e4 [0x48, 0x89, 0xCE] (fun s => s.RIP = 0x1083e4) (movR64R64Effect 0x1083e4 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1083e4 6 1).toInstrSpec (mov_r64_r64_effect_step 0x1083e4 0x48 0xce (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1083e7 [0x48, 0x21, 0xC6] (fun s => s.RIP = 0x1083e7) (andR64R64Effect 0x1083e7 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1083e7 6 0).toInstrSpec (and_r64_r64_effect_step 0x1083e7 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1083ea [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x1083ea) (orR64R64Effect 0x1083ea 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1083ea 0 1).toInstrSpec (or_r64_r64_effect_step 0x1083ea 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1083ed [0x48, 0x21, 0xD0] (fun s => s.RIP = 0x1083ed) (andR64R64Effect 0x1083ed 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1083ed 0 2).toInstrSpec (and_r64_r64_effect_step 0x1083ed 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1083f0 [0x48, 0x09, 0xF0] (fun s => s.RIP = 0x1083f0) (orR64R64Effect 0x1083f0 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1083f0 0 6).toInstrSpec (or_r64_r64_effect_step 0x1083f0 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1083f3 [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x1083f3) (shrR64Effect 0x1083f3 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x1083f3 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x1083f3 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1083f7 [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x1083f7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1083f7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1083f7 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1083f7 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1083f7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1083fc [0x48, 0x8D, 0x44, 0x24, 0x08] (fun s => s.RIP = 0x1083fc) (leaR64Effect 0x1083fc 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1083fc 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x1083fc 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x108401 [0x31, 0xC9] (fun s => s.RIP = 0x108401) (xorR32R32Effect 0x108401 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x108401 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x108401 0xc9 (by decide)) pre_rip
  have f14 : InstrSpec 0x108403 [0x31, 0xD2] (fun s => s.RIP = 0x108403) (xorR32R32Effect 0x108403 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x108403 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x108403 0xd2 (by decide)) pre_rip
  have f15 : InstrSpec 0x108405 [0x48, 0x2B, 0x54, 0x24, 0x08] (LoadPre 0x108405 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108405 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108405 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x108405 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x108405 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10840a [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x10840a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10840a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10840a 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10840a 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10840a 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10840f [0x48, 0x8B, 0x7B, 0x08] (LoadPre 0x10840f (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10840f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10840f 7 (.base 3 (.d8 0x8)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10840f 7 (.base 3 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10840f 0x48 (by decide) 7 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x108413 [0x48, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x108413) (sarR64Effect 0x108413 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (sarR64Effect_footprint 0x108413 4 2 63).toInstrSpec (sar_r64_imm8_effect_step 0x108413 0x48 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x108417 [0x48, 0x01, 0xF2] (fun s => s.RIP = 0x108417) (addR64R64Effect 0x108417 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x108417 2 6).toInstrSpec (add_r64_r64_effect_step 0x108417 0x48 0xf2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083d8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083db) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083de) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083e1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083e4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083e7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083ea) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083ed) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083f0) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083f3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083f7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 73), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1083fc) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108401) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 77), (2, 59), (3, 3), (4, 4), (5, 5), (6, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108403) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 77), (2, 79), (3, 3), (4, 4), (5, 5), (6, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108405) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(1, 77), (2, 81), (3, 3), (4, 4), (5, 5), (6, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10840a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(1, 77), (2, 81), (3, 3), (4, 4), (5, 5), (6, 83), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10840f) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(1, 77), (2, 81), (3, 3), (4, 4), (5, 5), (6, 83), (7, 85), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108413) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(1, 77), (2, 87), (3, 3), (4, 4), (5, 5), (6, 83), (7, 85), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108417) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(1, 77), (2, 89), (3, 3), (4, 4), (5, 5), (6, 83), (7, 85), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10841a) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1083d3_1 code

theorem block_l1083d3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1083d3 :=
  Rest.liftedBlock (rest_l1083d3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1083d3 x hx)

theorem rest_l1084af [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1084af bytes_l1084af) (entryMap (live .l1084af))
      3 0x1084af bytes_l1084af b_l1084af := by
  have f0 : InstrSpec 0x1084af [0x48, 0x83, 0xC4, 0x50] (fun s => s.RIP = 0x1084af) (addR64Imm8Effect 0x1084af 4 0x50)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1084af 4 0x50).toInstrSpec (add_r64_imm8_effect_step 0x1084af 0x48 0xc4 0x50 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1084b3 [0x5B] (PopPre 0x1084b3) (popR64Effect 0x1084b3 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1084b3 1 3).toInstrSpec (pop_r64_effect_step 0x1084b3 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1084b4 [0xC3] (RetPre 0x1084b4) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1084b4).toInstrSpec (ret_effect_step 0x1084b4) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084b3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084b4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f2 (by decide) rfl rfl rfl (by decide)

theorem block_l1084af [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1084af :=
  Rest.liftedBlock (rest_l1084af code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1084af x hx)

theorem rest_l1084c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1084c0 bytes_l1084c0) (entryMap (live .l1084c0))
      1 0x1084c0 bytes_l1084c0 b_l1084c0 := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x1084c0 0x201eb (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1084c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1084c0 :=
  Rest.liftedBlock (rest_l1084c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1084c0 x hx)

theorem rest_l1286b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1286b0 bytes_l1286b0) (entryMap (live .l1286b0))
      13 0x1286b0 bytes_l1286b0 b_l1286b0 := by
  have f0 : InstrSpec 0x1286b0 [0x55] (PushPre 0x1286b0 1) (pushR64Effect 0x1286b0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1286b0 1 5).toInstrSpec (push_r64_effect_step 0x1286b0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1286b1 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x1286b1) (movR64R64Effect 0x1286b1 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x1286b1 5 4).toInstrSpec (mov_r64_r64_effect_step 0x1286b1 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1286b4 [0x48, 0x83, 0xEC, 0x20] (fun s => s.RIP = 0x1286b4) (subR64Imm8Effect 0x1286b4 4 0x20)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1286b4 4 0x20).toInstrSpec (sub_r64_imm8_effect_step 0x1286b4 0x48 0xec 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1286b8 [0x48, 0x89, 0x7D, 0xF8] (StorePre 0x1286b8 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x1286b8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1286b8 7 (.base 5 (.d8 0xf8)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1286b8 7 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x1286b8 0x48 (by decide) 7 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1286bc [0x48, 0x8D, 0x45, 0xF8] (fun s => s.RIP = 0x1286bc) (leaR64Effect 0x1286bc 0 (.base 5 (.d8 0xf8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1286bc 0 (.base 5 (.d8 0xf8))).toInstrSpec (lea_r64_effect_step 0x1286bc 0x48 (by decide) 0 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1286c0 [0x48, 0x89, 0x45, 0xE8] (StorePre 0x1286c0 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x1286c0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1286c0 0 (.base 5 (.d8 0xe8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1286c0 0 (.base 5 (.d8 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x1286c0 0x48 (by decide) 0 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1286c4 [0x48, 0x8D, 0x05, 0x65, 0x1D, 0x00, 0x00] (fun s => s.RIP = 0x1286c4) (leaR64Effect 0x1286c4 0 (.rip 0x1d65))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1286c4 0 (.rip 0x1d65)).toInstrSpec (lea_r64_effect_step 0x1286c4 0x48 (by decide) 0 (.rip 0x1d65) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1286cb [0x48, 0x89, 0x45, 0xF0] (StorePre 0x1286cb 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x1286cb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1286cb 0 (.base 5 (.d8 0xf0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1286cb 0 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x1286cb 0x48 (by decide) 0 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1286cf [0x48, 0x8D, 0x3D, 0x4B, 0x88, 0x0D, 0x00] (fun s => s.RIP = 0x1286cf) (leaR64Effect 0x1286cf 7 (.rip 0xd884b))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1286cf 7 (.rip 0xd884b)).toInstrSpec (lea_r64_effect_step 0x1286cf 0x48 (by decide) 7 (.rip 0xd884b) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1286d6 [0x48, 0x8D, 0x0D, 0x5B, 0xB6, 0x0D, 0x00] (fun s => s.RIP = 0x1286d6) (leaR64Effect 0x1286d6 1 (.rip 0xdb65b))
      [] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x1286d6 1 (.rip 0xdb65b)).toInstrSpec (lea_r64_effect_step 0x1286d6 0x48 (by decide) 1 (.rip 0xdb65b) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1286dd [0x48, 0x8D, 0x75, 0xE8] (fun s => s.RIP = 0x1286dd) (leaR64Effect 0x1286dd 6 (.base 5 (.d8 0xe8)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1286dd 6 (.base 5 (.d8 0xe8))).toInstrSpec (lea_r64_effect_step 0x1286dd 0x48 (by decide) 6 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1286e1 [0x31, 0xD2] (fun s => s.RIP = 0x1286e1) (xorR32R32Effect 0x1286e1 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1286e1 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x1286e1 0xd2 (by decide)) pre_rip
  have f12 : InstrSpec 0x1286e3 [0xFF, 0x15, 0x0F, 0xB7, 0x0D, 0x00] (GoesTo (CallMemPre 0x1286e3 (.rip 0xdb70f)) (callEffect (callMemPtr 0x1286e3 (.rip 0xdb70f)) (0x1286e3 + BitVec.ofNat 64 (callMemLen (.rip 0xdb70f)))) 0x129630) (callEffect (callMemPtr 0x1286e3 (.rip 0xdb70f)) (0x1286e3 + BitVec.ofNat 64 (callMemLen (.rip 0xdb70f))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1286e3 (.rip 0xdb70f)).toInstrSpec (call_m64_effect_step 0x1286e3 (.rip 0xdb70f) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129630
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 53), (5, 5), (7, 7)]) (p' := 0x1286b1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 53), (5, 55), (7, 7)]) (p' := 0x1286b4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 57), (5, 55), (7, 7)]) (p' := 0x1286b8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(2, 2), (4, 57), (5, 55), (7, 7)]) (p' := 0x1286bc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (2, 2), (4, 57), (5, 55), (7, 7)]) (p' := 0x1286c0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 60), (2, 2), (4, 57), (5, 55), (7, 7)]) (p' := 0x1286c4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (2, 2), (4, 57), (5, 55), (7, 7)]) (p' := 0x1286cb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (2, 2), (4, 57), (5, 55), (7, 7)]) (p' := 0x1286cf) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 63), (2, 2), (4, 57), (5, 55), (7, 66)]) (p' := 0x1286d6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 63), (1, 68), (2, 2), (4, 57), (5, 55), (7, 66)]) (p' := 0x1286dd) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 63), (1, 68), (2, 2), (4, 57), (5, 55), (6, 70), (7, 66)]) (p' := 0x1286e1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 63), (1, 68), (2, 72), (4, 57), (5, 55), (6, 70), (7, 66)]) (p' := 0x1286e3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 63), (1, 68), (2, 72), (4, 74), (5, 55), (6, 70), (7, 66)]) (p' := 0x129630) f12 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 76) (by decide) (by decide) rfl rfl

theorem block_l1286b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1286b0 :=
  Rest.liftedBlock (rest_l1286b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1286b0 x hx)

theorem rest_l1084d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1084d0 bytes_l1084d0) (entryMap (live .l1084d0))
      1 0x1084d0 bytes_l1084d0 b_l1084d0 := by
  have f0 : InstrSpec 0x1084d0 [0xC3] (RetPre 0x1084d0) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1084d0).toInstrSpec (ret_effect_step 0x1084d0) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f0 (by decide) rfl rfl rfl (by decide)

theorem block_l1084d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1084d0 :=
  Rest.liftedBlock (rest_l1084d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1084d0 x hx)

theorem rest_l108890 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108890 bytes_l108890) (entryMap (live .l108890))
      8 0x108890 bytes_l108890 b_l108890 := by
  have f0 : InstrSpec 0x108890 [0x55] (PushPre 0x108890 1) (pushR64Effect 0x108890 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108890 1 5).toInstrSpec (push_r64_effect_step 0x108890 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x108891 [0x41, 0x56] (PushPre 0x108891 2) (pushR64Effect 0x108891 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108891 2 14).toInstrSpec (push_r64_rex_effect_step 0x108891 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x108893 [0x53] (PushPre 0x108893 1) (pushR64Effect 0x108893 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108893 1 3).toInstrSpec (push_r64_effect_step 0x108893 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x108894 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x108894) (subR64Imm8Effect 0x108894 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x108894 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x108894 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x108898 [0x44, 0x89, 0xCD] (fun s => s.RIP = 0x108898) (movR32R32Effect 0x108898 3 5 9)
      [.gpr 9] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x108898 3 5 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x108898 0x44 0xcd (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10889b [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x10889b) (movR64R64Effect 0x10889b 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10889b 3 7).toInstrSpec (mov_r64_r64_effect_step 0x10889b 0x48 0xfb (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10889e [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x10889e) (movR64R64Effect 0x10889e 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10889e 7 4).toInstrSpec (mov_r64_r64_effect_step 0x10889e 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1088a1 [0xE8, 0x3A, 0xFC, 0xFF, 0xFF] (PushPre 0x1088a1 5) (callEffect (fun _ => 0x1084e0) 0x1088a6)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1088a1 0x1084e0 0x1088a6).toInstrSpec (call_rel32_effect_step 0x1088a1 0xfffffc3a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108891) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108893) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108894) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108898) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 61), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10889b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 63), (4, 59), (5, 61), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10889e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 63), (4, 59), (5, 61), (6, 6), (7, 65), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088a1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 63), (4, 67), (5, 61), (6, 6), (7, 65), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084e0) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l108890 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108890 :=
  Rest.liftedBlock (rest_l108890 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108890 x hx)

theorem rest_l1088a6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1088a6 bytes_l1088a6) (entryMap (live .l1088a6))
      4 0x1088a6 bytes_l1088a6 b_l1088a6 := by
  have f0 : InstrSpec 0x1088a6 [0xB8, 0x40, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1088a6) (movR32Imm32Effect 0x1088a6 5 0 0x40)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1088a6 5 0 0x40).toInstrSpec (mov_r32_imm32_effect_step 0x1088a6 0xb8 (by decide) 0x40) pre_rip
  have f1 : InstrSpec 0x1088ab [0x29, 0xE8] (fun s => s.RIP = 0x1088ab) (subR32R32Effect 0x1088ab 2 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (subR32R32Effect_footprint 0x1088ab 2 0 5).toInstrSpec (sub_r32_r32_effect_step 0x1088ab 0xe8 (by decide)) pre_rip
  have f2 : InstrSpec 0x1088ad [0x83, 0xF8, 0x40] (fun s => s.RIP = 0x1088ad) (cmpR32Imm8Effect 0x1088ad 3 0 0x40)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1088ad 3 0 0x40).toInstrSpec (cmp_r32_imm8_effect_step 0x1088ad 0xf8 0x40 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088ab) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088ad) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088b0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x1088b0 3 0x9c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1088a6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1088a6 :=
  Rest.liftedBlock (rest_l1088a6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1088a6 x hx)

theorem rest_l1088b6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1088b6 bytes_l1088b6) (entryMap (live .l1088b6))
      2 0x1088b6 bytes_l1088b6 b_l1088b6 := by
  have f0 : InstrSpec 0x1088b6 [0x83, 0xFD, 0x40] (fun s => s.RIP = 0x1088b6) (cmpR32Imm8Effect 0x1088b6 3 5 0x40)
      [.gpr 5] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1088b6 3 5 0x40).toInstrSpec (cmp_r32_imm8_effect_step 0x1088b6 0xfd 0x40 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088b9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1088b9 3 0x7f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1088b6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1088b6 :=
  Rest.liftedBlock (rest_l1088b6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1088b6 x hx)

theorem rest_l1088bb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1088bb bytes_l1088bb) (entryMap (live .l1088bb))
      2 0x1088bb bytes_l1088bb b_l1088bb := by
  have f0 : InstrSpec 0x1088bb [0x85, 0xED] (fun s => s.RIP = 0x1088bb) (testR32R32Effect 0x1088bb 2 5 5)
      [.gpr 5, .gpr 5] [] [.flags, .rip] :=
    (testR32R32Effect_footprint 0x1088bb 2 5 5).toInstrSpec (test_r32_r32_effect_step 0x1088bb 0xed (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088bd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1088bd 4 0xa7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1088bb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1088bb :=
  Rest.liftedBlock (rest_l1088bb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1088bb x hx)

theorem rest_l1088c3_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x1088c3 bytes_l1088c3) [(0, 0), (1, 87), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 91), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      19 0x108906 bytes_l1088c3_1 b_l1088c3_1 := by
  have f20 : InstrSpec 0x108906 [0x89, 0xE9] (fun s => s.RIP = 0x108906) (movR32R32Effect 0x108906 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x108906 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x108906 0xe9 (by decide)) pre_rip
  have f21 : InstrSpec 0x108908 [0x49, 0xD3, 0xEE] (fun s => s.RIP = 0x108908) (shrR64ClEffect 0x108908 3 14)
      [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x108908 3 14).toInstrSpec (shr_r64_cl_effect_step 0x108908 0x49 0xee (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10890b [0x89, 0xC1] (fun s => s.RIP = 0x10890b) (movR32R32Effect 0x10890b 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10890b 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x10890b 0xc1 (by decide)) pre_rip
  have f23 : InstrSpec 0x10890d [0x48, 0xD3, 0xE6] (fun s => s.RIP = 0x10890d) (shlR64ClEffect 0x10890d 3 6)
      [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x10890d 3 6).toInstrSpec (shl_r64_cl_effect_step 0x10890d 0x48 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x108910 [0x89, 0xE9] (fun s => s.RIP = 0x108910) (movR32R32Effect 0x108910 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x108910 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x108910 0xe9 (by decide)) pre_rip
  have f25 : InstrSpec 0x108912 [0x48, 0xD3, 0xEA] (fun s => s.RIP = 0x108912) (shrR64ClEffect 0x108912 3 2)
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x108912 3 2).toInstrSpec (shr_r64_cl_effect_step 0x108912 0x48 0xea (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x108915 [0x4D, 0x09, 0xC3] (fun s => s.RIP = 0x108915) (orR64R64Effect 0x108915 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108915 11 8).toInstrSpec (or_r64_r64_effect_step 0x108915 0x4d 0xc3 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x108918 [0x49, 0x09, 0xFE] (fun s => s.RIP = 0x108918) (orR64R64Effect 0x108918 14 7)
      [.gpr 14, .gpr 7] [] [.reg 14, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108918 14 7).toInstrSpec (or_r64_r64_effect_step 0x108918 0x49 0xfe (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10891b [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x10891b) (orR64R64Effect 0x10891b 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10891b 2 6).toInstrSpec (or_r64_r64_effect_step 0x10891b 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x10891e [0x48, 0x89, 0x13] (StorePre 0x10891e 3 (fun s => AddrMode.addr (.base 3 .none) s (0x10891e + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10891e 2 (.base 3 .none))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10891e 2 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10891e 0x48 (by decide) 2 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x108921 [0x4C, 0x89, 0x73, 0x08] (StorePre 0x108921 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x108921 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108921 14 (.base 3 (.d8 0x8)))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x108921 14 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x108921 0x4c (by decide) 6 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x108925 [0x4C, 0x89, 0x5B, 0x10] (StorePre 0x108925 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x108925 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108925 11 (.base 3 (.d8 0x10)))
      [.gpr 11, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x108925 11 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x108925 0x4c (by decide) 3 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x108929 [0x4C, 0x89, 0x4B, 0x18] (StorePre 0x108929 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x108929 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108929 9 (.base 3 (.d8 0x18)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x108929 9 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x108929 0x4c (by decide) 1 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x10892d [0x44, 0x88, 0x53, 0x20] (StorePre 0x10892d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x10892d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10892d 4 10 (.base 3 (.d8 0x20)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x10892d 4 10 (.base 3 (.d8 0x20))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10892d 0x44 (by decide) 2 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x108931 [0x48, 0x83, 0xC4, 0x30] (fun s => s.RIP = 0x108931) (addR64Imm8Effect 0x108931 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x108931 4 0x30).toInstrSpec (add_r64_imm8_effect_step 0x108931 0x48 0xc4 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x108935 [0x5B] (PopPre 0x108935) (popR64Effect 0x108935 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x108935 1 3).toInstrSpec (pop_r64_effect_step 0x108935 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f36 : InstrSpec 0x108936 [0x41, 0x5E] (PopPre 0x108936) (popR64Effect 0x108936 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x108936 2 14).toInstrSpec (pop_r64_rex_effect_step 0x108936 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f37 : InstrSpec 0x108938 [0x5D] (PopPre 0x108938) (popR64Effect 0x108938 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x108938 1 5).toInstrSpec (pop_r64_effect_step 0x108938 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f38 : InstrSpec 0x108939 [0xC3] (RetPre 0x108939) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x108939).toInstrSpec (ret_effect_step 0x108939) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 0), (1, 93), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 91), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108908) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 0), (1, 93), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10890b) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 0), (1, 97), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10890d) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 0), (1, 97), (2, 53), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108910) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 0), (1, 101), (2, 53), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108912) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 0), (1, 101), (2, 103), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108915) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 0), (1, 101), (2, 103), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108918) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 0), (1, 101), (2, 103), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10891b) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10891e) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.exec (n := 111) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108921) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 112) (RestInside.exec (n := 112) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108925) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 113) (RestInside.exec (n := 113) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108929) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 114) (RestInside.exec (n := 114) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10892d) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 115) (RestInside.exec (n := 115) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108931) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f34 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 116), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108935) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f35 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 119) f35 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 120) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 118), (4, 119), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108936) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 122) f36 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 123) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 118), (4, 122), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 121), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108938) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f37 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 125) f37 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 126) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 118), (4, 125), (5, 124), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 121), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108939) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f38 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 128) f38 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 129) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 118), (4, 128), (5, 124), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 121), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f38 (by decide) rfl rfl rfl (by decide)

theorem rest_l1088c3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1088c3 bytes_l1088c3) (entryMap (live .l1088c3))
      39 0x1088c3 bytes_l1088c3 b_l1088c3 := by
  have f0 : InstrSpec 0x1088c3 [0x48, 0x8B, 0x14, 0x24] (LoadPre 0x1088c3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1088c3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1088c3 2 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1088c3 2 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1088c3 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1088c7 [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x1088c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1088c7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1088c7 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1088c7 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1088c7 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1088cc [0x48, 0x8B, 0x7C, 0x24, 0x10] (LoadPre 0x1088cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1088cc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1088cc 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1088cc 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1088cc 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1088d1 [0x4C, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x1088d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1088d1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1088d1 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1088d1 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1088d1 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1088d6 [0x4C, 0x8B, 0x5C, 0x24, 0x20] (LoadPre 0x1088d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1088d6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1088d6 11 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1088d6 11 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1088d6 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1088db [0x89, 0xC1] (fun s => s.RIP = 0x1088db) (movR32R32Effect 0x1088db 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1088db 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1088db 0xc1 (by decide)) pre_rip
  have f6 : InstrSpec 0x1088dd [0x49, 0xD3, 0xE3] (fun s => s.RIP = 0x1088dd) (shlR64ClEffect 0x1088dd 3 11)
      [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x1088dd 3 11).toInstrSpec (shl_r64_cl_effect_step 0x1088dd 0x49 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1088e0 [0x4D, 0x89, 0xC1] (fun s => s.RIP = 0x1088e0) (movR64R64Effect 0x1088e0 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x1088e0 9 8).toInstrSpec (mov_r64_r64_effect_step 0x1088e0 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1088e3 [0x89, 0xE9] (fun s => s.RIP = 0x1088e3) (movR32R32Effect 0x1088e3 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1088e3 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x1088e3 0xe9 (by decide)) pre_rip
  have f9 : InstrSpec 0x1088e5 [0x49, 0xD3, 0xE9] (fun s => s.RIP = 0x1088e5) (shrR64ClEffect 0x1088e5 3 9)
      [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x1088e5 3 9).toInstrSpec (shr_r64_cl_effect_step 0x1088e5 0x49 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1088e8 [0x89, 0xC1] (fun s => s.RIP = 0x1088e8) (movR32R32Effect 0x1088e8 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1088e8 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1088e8 0xc1 (by decide)) pre_rip
  have f11 : InstrSpec 0x1088ea [0x49, 0xD3, 0xE0] (fun s => s.RIP = 0x1088ea) (shlR64ClEffect 0x1088ea 3 8)
      [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x1088ea 3 8).toInstrSpec (shl_r64_cl_effect_step 0x1088ea 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1088ed [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x28] (LoadPre 0x1088ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1088ed + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1088ed 6 10 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x1088ed 6 10 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1088ed 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1088f3 [0x4D, 0x09, 0xD9] (fun s => s.RIP = 0x1088f3) (orR64R64Effect 0x1088f3 9 11)
      [.gpr 9, .gpr 11] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1088f3 9 11).toInstrSpec (or_r64_r64_effect_step 0x1088f3 0x4d 0xd9 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1088f6 [0x49, 0x89, 0xFB] (fun s => s.RIP = 0x1088f6) (movR64R64Effect 0x1088f6 11 7)
      [.gpr 7] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x1088f6 11 7).toInstrSpec (mov_r64_r64_effect_step 0x1088f6 0x49 0xfb (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1088f9 [0x89, 0xE9] (fun s => s.RIP = 0x1088f9) (movR32R32Effect 0x1088f9 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1088f9 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x1088f9 0xe9 (by decide)) pre_rip
  have f16 : InstrSpec 0x1088fb [0x49, 0xD3, 0xEB] (fun s => s.RIP = 0x1088fb) (shrR64ClEffect 0x1088fb 3 11)
      [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x1088fb 3 11).toInstrSpec (shr_r64_cl_effect_step 0x1088fb 0x49 0xeb (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1088fe [0x89, 0xC1] (fun s => s.RIP = 0x1088fe) (movR32R32Effect 0x1088fe 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1088fe 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1088fe 0xc1 (by decide)) pre_rip
  have f18 : InstrSpec 0x108900 [0x48, 0xD3, 0xE7] (fun s => s.RIP = 0x108900) (shlR64ClEffect 0x108900 3 7)
      [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x108900 3 7).toInstrSpec (shl_r64_cl_effect_step 0x108900 0x48 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x108903 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x108903) (movR64R64Effect 0x108903 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x108903 14 6).toInstrSpec (mov_r64_r64_effect_step 0x108903 0x49 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088c7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088cc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088d1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088d6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (11, 61), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088db) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (11, 61), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088dd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 63), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088e0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 63), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 67), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088e3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 69), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 67), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088e5) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 69), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 71), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088e8) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 73), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 71), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088ea) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 73), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 71), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088ed) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 73), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 71), (10, 77), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088f3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 73), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 79), (10, 77), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088f6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 73), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 79), (10, 77), (11, 81), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088f9) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 83), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 79), (10, 77), (11, 81), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088fb) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 83), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088fe) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 87), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108900) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 87), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108903) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 87), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 91), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108906) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1088c3_1 code

theorem block_l1088c3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1088c3 :=
  Rest.liftedBlock (rest_l1088c3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1088c3 x hx)

theorem rest_l10893a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10893a bytes_l10893a) (entryMap (live .l10893a))
      4 0x10893a bytes_l10893a b_l10893a := by
  have f0 : InstrSpec 0x10893a [0xBE, 0x1B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10893a) (movR32Imm32Effect 0x10893a 5 6 0x1b)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10893a 5 6 0x1b).toInstrSpec (mov_r32_imm32_effect_step 0x10893a 0xbe (by decide) 0x1b) pre_rip
  have f1 : InstrSpec 0x10893f [0x48, 0xC7, 0xC7, 0x38, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x10893f) (movR64Imm32Effect 0x10893f 7 0x202b38)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x10893f 7 0x202b38).toInstrSpec (mov_r64_imm32_effect_step 0x10893f 0x48 0xc7 (by decide) (by decide) (by decide) 0x202b38) pre_rip
  have f2 : InstrSpec 0x108946 [0x48, 0xC7, 0xC2, 0x58, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x108946) (movR64Imm32Effect 0x108946 2 0x202b58)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x108946 2 0x202b58).toInstrSpec (mov_r64_imm32_effect_step 0x108946 0x48 0xc2 (by decide) (by decide) (by decide) 0x202b58) pre_rip
  have f3 : InstrSpec 0x10894d [0xE8, 0x0E, 0x0C, 0x02, 0x00] (PushPre 0x10894d 5) (callEffect (fun _ => 0x129560) 0x108952)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10894d 0x129560 0x108952).toInstrSpec (call_rel32_effect_step 0x10894d 0x20c0e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 53)]) (p' := 0x10893f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x108946) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x10894d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)]) (p' := 0x129560) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10893a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10893a :=
  Rest.liftedBlock (rest_l10893a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10893a x hx)

theorem rest_l108952 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108952 bytes_l108952) (entryMap (live .l108952))
      4 0x108952 bytes_l108952 b_l108952 := by
  have f0 : InstrSpec 0x108952 [0xBE, 0x1B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108952) (movR32Imm32Effect 0x108952 5 6 0x1b)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x108952 5 6 0x1b).toInstrSpec (mov_r32_imm32_effect_step 0x108952 0xbe (by decide) 0x1b) pre_rip
  have f1 : InstrSpec 0x108957 [0x48, 0xC7, 0xC7, 0x38, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x108957) (movR64Imm32Effect 0x108957 7 0x202b38)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x108957 7 0x202b38).toInstrSpec (mov_r64_imm32_effect_step 0x108957 0x48 0xc7 (by decide) (by decide) (by decide) 0x202b38) pre_rip
  have f2 : InstrSpec 0x10895e [0x48, 0xC7, 0xC2, 0x08, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x10895e) (movR64Imm32Effect 0x10895e 2 0x202b08)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10895e 2 0x202b08).toInstrSpec (mov_r64_imm32_effect_step 0x10895e 0x48 0xc2 (by decide) (by decide) (by decide) 0x202b08) pre_rip
  have f3 : InstrSpec 0x108965 [0xE8, 0xF6, 0x0B, 0x02, 0x00] (PushPre 0x108965 5) (callEffect (fun _ => 0x129560) 0x10896a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x108965 0x129560 0x10896a).toInstrSpec (call_rel32_effect_step 0x108965 0x20bf6 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 53)]) (p' := 0x108957) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x10895e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x108965) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)]) (p' := 0x129560) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l108952 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108952 :=
  Rest.liftedBlock (rest_l108952 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108952 x hx)

theorem rest_l10896a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10896a bytes_l10896a) (entryMap (live .l10896a))
      4 0x10896a bytes_l10896a b_l10896a := by
  have f0 : InstrSpec 0x10896a [0xBF, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10896a) (movR32Imm32Effect 0x10896a 5 7 0x4)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x10896a 5 7 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x10896a 0xbf (by decide) 0x4) pre_rip
  have f1 : InstrSpec 0x10896f [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10896f) (movR32Imm32Effect 0x10896f 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10896f 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x10896f 0xbe (by decide) 0x4) pre_rip
  have f2 : InstrSpec 0x108974 [0x48, 0xC7, 0xC2, 0x20, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x108974) (movR64Imm32Effect 0x108974 2 0x202b20)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x108974 2 0x202b20).toInstrSpec (mov_r64_imm32_effect_step 0x108974 0x48 0xc2 (by decide) (by decide) (by decide) 0x202b20) pre_rip
  have f3 : InstrSpec 0x10897b [0xE8, 0x72, 0x0C, 0x02, 0x00] (PushPre 0x10897b 5) (callEffect (fun _ => 0x1295f2) 0x108980)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10897b 0x1295f2 0x108980).toInstrSpec (call_rel32_effect_step 0x10897b 0x20c72 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x10896f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x108974) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10897b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x1295f2) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10896a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10896a :=
  Rest.liftedBlock (rest_l10896a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10896a x hx)

theorem rest_l109d80 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109d80 bytes_l109d80) (entryMap (live .l109d80))
      12 0x109d80 bytes_l109d80 b_l109d80 := by
  have f0 : InstrSpec 0x109d80 [0x41, 0x57] (PushPre 0x109d80 2) (pushR64Effect 0x109d80 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109d80 2 15).toInstrSpec (push_r64_rex_effect_step 0x109d80 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x109d82 [0x41, 0x56] (PushPre 0x109d82 2) (pushR64Effect 0x109d82 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109d82 2 14).toInstrSpec (push_r64_rex_effect_step 0x109d82 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x109d84 [0x41, 0x55] (PushPre 0x109d84 2) (pushR64Effect 0x109d84 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109d84 2 13).toInstrSpec (push_r64_rex_effect_step 0x109d84 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x109d86 [0x41, 0x54] (PushPre 0x109d86 2) (pushR64Effect 0x109d86 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109d86 2 12).toInstrSpec (push_r64_rex_effect_step 0x109d86 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x109d88 [0x53] (PushPre 0x109d88 1) (pushR64Effect 0x109d88 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109d88 1 3).toInstrSpec (push_r64_effect_step 0x109d88 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x109d89 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x109d89) (subR64Imm8Effect 0x109d89 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x109d89 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x109d89 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x109d8d [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x109d8d) (movR64R64Effect 0x109d8d 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x109d8d 3 7).toInstrSpec (mov_r64_r64_effect_step 0x109d8d 0x48 0xfb (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x109d90 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x109d90) (leaR64Effect 0x109d90 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x109d90 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x109d90 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x109d95 [0x48, 0xB9, 0xC1, 0x4E, 0x77, 0xAA, 0x99, 0x00, 0xF2, 0xB4] (fun s => s.RIP = 0x109d95) (movR64Imm64Effect 0x109d95 1 0xb4f20099aa774ec1)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x109d95 1 0xb4f20099aa774ec1).toInstrSpec (mov_r64_imm64_effect_step 0x109d95 0x48 0xb9 (by decide) (by decide) 0xb4f20099aa774ec1) pre_rip
  have f9 : InstrSpec 0x109d9f [0x48, 0xC7, 0xC2, 0xA0, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x109d9f) (movR64Imm32Effect 0x109d9f 2 0x2021a0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x109d9f 2 0x2021a0).toInstrSpec (mov_r64_imm32_effect_step 0x109d9f 0x48 0xc2 (by decide) (by decide) (by decide) 0x2021a0) pre_rip
  have f10 : InstrSpec 0x109da6 [0x49, 0xC7, 0xC0, 0x80, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x109da6) (movR64Imm32Effect 0x109da6 8 0x202180)
      [] [] [.reg 8, .rip] :=
    (movR64Imm32Effect_footprint 0x109da6 8 0x202180).toInstrSpec (mov_r64_imm32_effect_step 0x109da6 0x49 0xc0 (by decide) (by decide) (by decide) 0x202180) pre_rip
  have f11 : InstrSpec 0x109dad [0xE8, 0x7E, 0xF0, 0xFF, 0xFF] (PushPre 0x109dad 5) (callEffect (fun _ => 0x108e30) 0x109db2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109dad 0x108e30 0x109db2).toInstrSpec (call_rel32_effect_step 0x109dad 0xfffff07e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d82) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d84) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d86) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d88) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d89) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d8d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d90) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(3, 65), (4, 63), (5, 5), (6, 6), (7, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d95) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 69), (3, 65), (4, 63), (5, 5), (6, 6), (7, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d9f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 69), (2, 71), (3, 65), (4, 63), (5, 5), (6, 6), (7, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109da6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 69), (2, 71), (3, 65), (4, 63), (5, 5), (6, 6), (7, 67), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109dad) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 69), (2, 71), (3, 65), (4, 75), (5, 5), (6, 6), (7, 67), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e30) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l109d80 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109d80 :=
  Rest.liftedBlock (rest_l109d80 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109d80 x hx)

theorem rest_l109db2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109db2 bytes_l109db2) (entryMap (live .l109db2))
      6 0x109db2 bytes_l109db2 b_l109db2 := by
  have f0 : InstrSpec 0x109db2 [0x4C, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x109db2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109db2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109db2 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x109db2 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109db2 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x109db7 [0x4C, 0x8B, 0x7C, 0x24, 0x10] (LoadPre 0x109db7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109db7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109db7 15 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x109db7 15 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x109db7 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x109dbc [0x4C, 0x8B, 0x64, 0x24, 0x18] (LoadPre 0x109dbc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109dbc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109dbc 12 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x109dbc 12 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x109dbc 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x109dc1 [0x4C, 0x8B, 0x6C, 0x24, 0x20] (LoadPre 0x109dc1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109dc1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109dc1 13 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x109dc1 13 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x109dc1 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x109dc6 [0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x109dc6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109dc6 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x109dc6 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x109dc6 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r32_m32_low_effect_step 0x109dc6 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x109dca [0xE8, 0x81, 0xDF, 0x01, 0x00] (PushPre 0x109dca 5) (callEffect (fun _ => 0x127d50) 0x109dcf)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109dca 0x127d50 0x109dcf).toInstrSpec (call_rel32_effect_step 0x109dca 0x1df81 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109db7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109dbc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109dc1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109dc6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109dca) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l109db2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109db2 :=
  Rest.liftedBlock (rest_l109db2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109db2 x hx)

theorem rest_l109dcf_1 [Bindings] (code : CodeMap) :
    Rest (n := 86) code lifted (codeRange 0x109dcf bytes_l109dcf) [(0, 0), (1, 55), (2, 79), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]
      8 0x109e10 bytes_l109dcf_1 b_l109dcf_1 := by
  have f20 : InstrSpec 0x109e10 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x109e10) (movR64R64Effect 0x109e10 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109e10 0 3).toInstrSpec (mov_r64_r64_effect_step 0x109e10 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x109e13 [0x48, 0x83, 0xC4, 0x30] (fun s => s.RIP = 0x109e13) (addR64Imm8Effect 0x109e13 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x109e13 4 0x30).toInstrSpec (add_r64_imm8_effect_step 0x109e13 0x48 0xc4 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x109e17 [0x5B] (PopPre 0x109e17) (popR64Effect 0x109e17 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109e17 1 3).toInstrSpec (pop_r64_effect_step 0x109e17 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f23 : InstrSpec 0x109e18 [0x41, 0x5C] (PopPre 0x109e18) (popR64Effect 0x109e18 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109e18 2 12).toInstrSpec (pop_r64_rex_effect_step 0x109e18 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f24 : InstrSpec 0x109e1a [0x41, 0x5D] (PopPre 0x109e1a) (popR64Effect 0x109e1a 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109e1a 2 13).toInstrSpec (pop_r64_rex_effect_step 0x109e1a 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f25 : InstrSpec 0x109e1c [0x41, 0x5E] (PopPre 0x109e1c) (popR64Effect 0x109e1c 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109e1c 2 14).toInstrSpec (pop_r64_rex_effect_step 0x109e1c 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f26 : InstrSpec 0x109e1e [0x41, 0x5F] (PopPre 0x109e1e) (popR64Effect 0x109e1e 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109e1e 2 15).toInstrSpec (pop_r64_rex_effect_step 0x109e1e 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f27 : InstrSpec 0x109e20 [0xC3] (RetPre 0x109e20) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x109e20).toInstrSpec (ret_effect_step 0x109e20) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 86), (1, 55), (2, 79), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e13) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f21 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 86), (1, 55), (2, 79), (3, 3), (4, 88), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e17) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f22 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 91) f22 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 92) (ρ' := [(0, 86), (1, 55), (2, 79), (3, 90), (4, 91), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e18) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f23 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 94) f23 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 95) (ρ' := [(0, 86), (1, 55), (2, 79), (3, 90), (4, 94), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 93), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e1a) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f24 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 97) f24 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 98) (ρ' := [(0, 86), (1, 55), (2, 79), (3, 90), (4, 97), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 93), (13, 96), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e1c) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f25 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 100) f25 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 101) (ρ' := [(0, 86), (1, 55), (2, 79), (3, 90), (4, 100), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 93), (13, 96), (14, 99), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e1e) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f26 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 103) f26 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 104) (ρ' := [(0, 86), (1, 55), (2, 79), (3, 90), (4, 103), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 93), (13, 96), (14, 99), (15, 102), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e20) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 106) f27 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 107) (ρ' := [(0, 86), (1, 55), (2, 79), (3, 90), (4, 106), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 93), (13, 96), (14, 99), (15, 102), (22, 22), (39, 39), (50, 50), (51, 51)]) f27 (by decide) rfl rfl rfl (by decide)

theorem rest_l109dcf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109dcf bytes_l109dcf) (entryMap (live .l109dcf))
      28 0x109dcf bytes_l109dcf b_l109dcf := by
  have f0 : InstrSpec 0x109dcf [0x88, 0x44, 0x24, 0x07] (StorePre 0x109dcf 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109dcf + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109dcf 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109dcf 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x109dcf 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x109dd3 [0x48, 0x8D, 0x4C, 0x24, 0x07] (fun s => s.RIP = 0x109dd3) (leaR64Effect 0x109dd3 1 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x109dd3 1 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x109dd3 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x109dd8 [0x0F, 0xB6, 0x4C, 0x24, 0x07] (LoadPre 0x109dd8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109dd8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109dd8 5 1 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109dd8 5 1 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x109dd8 1 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x109ddd [0x31, 0xD2] (fun s => s.RIP = 0x109ddd) (xorR32R32Effect 0x109ddd 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109ddd 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x109ddd 0xd2 (by decide)) pre_rip
  have f4 : InstrSpec 0x109ddf [0x31, 0xF6] (fun s => s.RIP = 0x109ddf) (xorR32R32Effect 0x109ddf 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109ddf 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x109ddf 0xf6 (by decide)) pre_rip
  have f5 : InstrSpec 0x109de1 [0x84, 0xC9] (fun s => s.RIP = 0x109de1) (testR8R8Effect 0x109de1 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x109de1 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x109de1 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x109de3 [0x49, 0x0F, 0x45, 0xF6] (fun s => s.RIP = 0x109de3) (atFlags (condHolds 5) (cmovR64R64Effect 0x109de3 4 6 14))
      [.gpr 6, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 6, .rip] :=
    (cmovR64R64Effect_footprint 0x109de3 4 6 14 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x109de3 5 0x49 (by decide) 0xf6 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x109de7 [0x31, 0xFF] (fun s => s.RIP = 0x109de7) (xorR32R32Effect 0x109de7 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109de7 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x109de7 0xff (by decide)) pre_rip
  have f8 : InstrSpec 0x109de9 [0x84, 0xC9] (fun s => s.RIP = 0x109de9) (testR8R8Effect 0x109de9 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x109de9 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x109de9 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x109deb [0x49, 0x0F, 0x45, 0xFF] (fun s => s.RIP = 0x109deb) (atFlags (condHolds 5) (cmovR64R64Effect 0x109deb 4 7 15))
      [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (cmovR64R64Effect_footprint 0x109deb 4 7 15 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x109deb 5 0x49 (by decide) 0xff (by decide) c)) pre_rip
  have f10 : InstrSpec 0x109def [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x109def) (xorR32R32Effect 0x109def 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109def 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x109def 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x109df2 [0x84, 0xC9] (fun s => s.RIP = 0x109df2) (testR8R8Effect 0x109df2 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x109df2 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x109df2 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x109df4 [0x4D, 0x0F, 0x45, 0xC4] (fun s => s.RIP = 0x109df4) (atFlags (condHolds 5) (cmovR64R64Effect 0x109df4 4 8 12))
      [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 8, .rip] :=
    (cmovR64R64Effect_footprint 0x109df4 4 8 12 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x109df4 5 0x4d (by decide) 0xc4 (by decide) c)) pre_rip
  have f13 : InstrSpec 0x109df8 [0x84, 0xC9] (fun s => s.RIP = 0x109df8) (testR8R8Effect 0x109df8 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x109df8 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x109df8 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x109dfa [0x49, 0x0F, 0x45, 0xD5] (fun s => s.RIP = 0x109dfa) (atFlags (condHolds 5) (cmovR64R64Effect 0x109dfa 4 2 13))
      [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x109dfa 4 2 13 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x109dfa 5 0x49 (by decide) 0xd5 (by decide) c)) pre_rip
  have f15 : InstrSpec 0x109dfe [0x48, 0x89, 0x33] (StorePre 0x109dfe 3 (fun s => AddrMode.addr (.base 3 .none) s (0x109dfe + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x109dfe 6 (.base 3 .none))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x109dfe 6 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x109dfe 0x48 (by decide) 6 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x109e01 [0x48, 0x89, 0x7B, 0x08] (StorePre 0x109e01 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x109e01 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e01 7 (.base 3 (.d8 0x8)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x109e01 7 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109e01 0x48 (by decide) 7 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x109e05 [0x4C, 0x89, 0x43, 0x10] (StorePre 0x109e05 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x109e05 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e05 8 (.base 3 (.d8 0x10)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x109e05 8 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x109e05 0x4c (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x109e09 [0x48, 0x89, 0x53, 0x18] (StorePre 0x109e09 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x109e09 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e09 2 (.base 3 (.d8 0x18)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x109e09 2 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x109e09 0x48 (by decide) 2 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x109e0d [0x88, 0x43, 0x20] (StorePre 0x109e0d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x109e0d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109e0d 3 0 (.base 3 (.d8 0x20)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x109e0d 3 0 (.base 3 (.d8 0x20))).toInstrSpec (mov_m8_r8_effect_step 0x109e0d 0 (by decide) (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109dd3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109dd8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ddd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ddf) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109de1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109de3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109de7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109de9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109deb) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109def) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 71), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109df2) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 71), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109df4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109df8) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109dfa) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 55), (2, 79), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109dfe) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 55), (2, 79), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e01) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 55), (2, 79), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e05) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 55), (2, 79), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e09) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 55), (2, 79), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e0d) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 55), (2, 79), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e10) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l109dcf_1 code

theorem block_l109dcf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109dcf :=
  Rest.liftedBlock (rest_l109dcf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109dcf x hx)

theorem rest_l109e30 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109e30 bytes_l109e30) (entryMap (live .l109e30))
      14 0x109e30 bytes_l109e30 b_l109e30 := by
  have f0 : InstrSpec 0x109e30 [0x48, 0x8B, 0x4E, 0x18] (LoadPre 0x109e30 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x109e30 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e30 1 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109e30 1 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x109e30 0x48 (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x109e34 [0x48, 0x0F, 0xC9] (fun s => s.RIP = 0x109e34) (bswapR64Effect 0x109e34 3 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR64Effect_footprint 0x109e34 3 1).toInstrSpec (bswap_r64_effect_step 0x109e34 0x48 (by decide) 0xc9 (by decide)) pre_rip
  have f2 : InstrSpec 0x109e37 [0x48, 0x8B, 0x56, 0x10] (LoadPre 0x109e37 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x109e37 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e37 2 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x109e37 2 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x109e37 0x48 (by decide) 2 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x109e3b [0x48, 0x0F, 0xCA] (fun s => s.RIP = 0x109e3b) (bswapR64Effect 0x109e3b 3 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR64Effect_footprint 0x109e3b 3 2).toInstrSpec (bswap_r64_effect_step 0x109e3b 0x48 (by decide) 0xca (by decide)) pre_rip
  have f4 : InstrSpec 0x109e3e [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x109e3e) (movR64R64Effect 0x109e3e 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109e3e 0 7).toInstrSpec (mov_r64_r64_effect_step 0x109e3e 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x109e41 [0x48, 0x8B, 0x7E, 0x08] (LoadPre 0x109e41 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109e41 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e41 7 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x109e41 7 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109e41 0x48 (by decide) 7 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x109e45 [0x48, 0x0F, 0xCF] (fun s => s.RIP = 0x109e45) (bswapR64Effect 0x109e45 3 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (bswapR64Effect_footprint 0x109e45 3 7).toInstrSpec (bswap_r64_effect_step 0x109e45 0x48 (by decide) 0xcf (by decide)) pre_rip
  have f7 : InstrSpec 0x109e48 [0x48, 0x8B, 0x36] (LoadPre 0x109e48 (fun s => AddrMode.addr (.base 6 .none) s (0x109e48 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109e48 6 (.base 6 .none))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x109e48 6 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x109e48 0x48 (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x109e4b [0x48, 0x0F, 0xCE] (fun s => s.RIP = 0x109e4b) (bswapR64Effect 0x109e4b 3 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (bswapR64Effect_footprint 0x109e4b 3 6).toInstrSpec (bswap_r64_effect_step 0x109e4b 0x48 (by decide) 0xce (by decide)) pre_rip
  have f9 : InstrSpec 0x109e4e [0x48, 0x89, 0x08] (StorePre 0x109e4e 3 (fun s => AddrMode.addr (.base 0 .none) s (0x109e4e + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x109e4e 1 (.base 0 .none))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x109e4e 1 (.base 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x109e4e 0x48 (by decide) 1 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x109e51 [0x48, 0x89, 0x50, 0x08] (StorePre 0x109e51 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x109e51 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e51 2 (.base 0 (.d8 0x8)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x109e51 2 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109e51 0x48 (by decide) 2 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x109e55 [0x48, 0x89, 0x78, 0x10] (StorePre 0x109e55 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x109e55 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e55 7 (.base 0 (.d8 0x10)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x109e55 7 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x109e55 0x48 (by decide) 7 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x109e59 [0x48, 0x89, 0x70, 0x18] (StorePre 0x109e59 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x109e59 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e59 6 (.base 0 (.d8 0x18)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x109e59 6 (.base 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x109e59 0x48 (by decide) 6 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x109e5d [0xC3] (RetPre 0x109e5d) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x109e5d).toInstrSpec (ret_effect_step 0x109e5d) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e34) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e37) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e3b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e3e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e41) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e45) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e48) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e4b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e4e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e51) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e55) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e59) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e5d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 76), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f13 (by decide) rfl rfl rfl (by decide)

theorem block_l109e30 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109e30 :=
  Rest.liftedBlock (rest_l109e30 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109e30 x hx)

theorem rest_l109e60_2 [Bindings] (code : CodeMap) :
    Rest (n := 130) code lifted (codeRange 0x109e60 bytes_l109e60) [(1, 97), (2, 124), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]
      18 0x109eef bytes_l109e60_2 b_l109e60_2 := by
  have f40 : InstrSpec 0x109eef [0x4C, 0x01, 0xFA] (fun s => s.RIP = 0x109eef) (addR64R64Effect 0x109eef 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109eef 2 15).toInstrSpec (add_r64_r64_effect_step 0x109eef 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x109ef2 [0x48, 0x83, 0xC2, 0x02] (fun s => s.RIP = 0x109ef2) (addR64Imm8Effect 0x109ef2 2 0x2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x109ef2 2 0x2).toInstrSpec (add_r64_imm8_effect_step 0x109ef2 0x48 0xc2 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x109ef6 [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x109ef6) (orR64R64Effect 0x109ef6 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109ef6 2 6).toInstrSpec (or_r64_r64_effect_step 0x109ef6 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x109ef9 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x109ef9) (shrR64Effect 0x109ef9 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x109ef9 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x109ef9 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x109efd [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x109efd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109efd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109efd 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109efd 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109efd 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x109f02 [0x48, 0x2B, 0x4C, 0x24, 0x08] (LoadPre 0x109f02 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109f02 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109f02 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x109f02 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x109f02 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f46 : InstrSpec 0x109f07 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x109f07) (sarR64Effect 0x109f07 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x109f07 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x109f07 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x109f0b [0x4C, 0x01, 0xF1] (fun s => s.RIP = 0x109f0b) (addR64R64Effect 0x109f0b 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109f0b 1 14).toInstrSpec (add_r64_r64_effect_step 0x109f0b 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x109f0e [0x48, 0xFF, 0xC1] (fun s => s.RIP = 0x109f0e) (incR64Effect 0x109f0e 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (incR64Effect_footprint 0x109f0e 1).toInstrSpec (inc_r64_effect_step 0x109f0e 0x48 0xc1 (by decide) (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x109f11 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x109f11) (movR64R64Effect 0x109f11 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x109f11 2 14).toInstrSpec (mov_r64_r64_effect_step 0x109f11 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x109f14 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x109f14) (notR64Effect 0x109f14 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x109f14 2).toInstrSpec (not_r64_effect_step 0x109f14 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x109f17 [0x48, 0x09, 0xCA] (fun s => s.RIP = 0x109f17) (orR64R64Effect 0x109f17 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109f17 2 1).toInstrSpec (or_r64_r64_effect_step 0x109f17 0x48 0xca (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x109f1a [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x109f1a) (shrR64Effect 0x109f1a 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x109f1a 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x109f1a 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x109f1e [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x109f1e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109f1e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109f1e 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109f1e 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109f1e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x109f23 [0x0F, 0xB6, 0x44, 0x24, 0x08] (LoadPre 0x109f23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109f23 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109f23 5 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109f23 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x109f23 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f55 : InstrSpec 0x109f28 [0x24, 0x01] (fun s => s.RIP = 0x109f28) (andAlImm8Effect 0x109f28 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x109f28 0x1).toInstrSpec (and_al_imm8_effect_step 0x109f28 0x1) pre_rip
  have f56 : InstrSpec 0x109f2a [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x109f2a) (movzxR32R8Effect 0x109f2a 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x109f2a 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x109f2a 0xf8 (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x109f2d [0xE8, 0x1E, 0xDE, 0x01, 0x00] (PushPre 0x109f2d 5) (callEffect (fun _ => 0x127d50) 0x109f32)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109f2d 0x127d50 0x109f32).toInstrSpec (call_rel32_effect_step 0x109f2d 0x1de1e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f40 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(1, 97), (2, 130), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ef2) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f41 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(1, 97), (2, 132), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ef6) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f42 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(1, 97), (2, 134), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ef9) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f43 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(1, 97), (2, 136), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109efd) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.exec (n := 138) (ρ' := [(1, 97), (2, 136), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f02) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f45 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(1, 139), (2, 136), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f07) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(1, 141), (2, 136), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f0b) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f47 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(1, 143), (2, 136), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f0e) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f48 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(1, 145), (2, 136), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f11) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f49 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(1, 145), (2, 147), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f14) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f50 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(1, 145), (2, 149), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f17) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f51 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(1, 145), (2, 151), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f1a) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f52 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(1, 145), (2, 153), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f1e) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.exec (n := 155) (ρ' := [(1, 145), (2, 153), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f23) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f54 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 156), (1, 145), (2, 153), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f28) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f55 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 158), (1, 145), (2, 153), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f2a) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f56 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 158), (1, 145), (2, 153), (3, 65), (4, 63), (5, 5), (6, 128), (7, 160), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f2d) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f57 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 158), (1, 145), (2, 153), (3, 65), (4, 162), (5, 5), (6, 128), (7, 160), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f57 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 164) (by decide) (by decide) rfl rfl

theorem rest_l109e60_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x109e60 bytes_l109e60) [(0, 85), (1, 91), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]
      38 0x109ea1 bytes_l109e60_1 b_l109e60_1 := by
  have f20 : InstrSpec 0x109ea1 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x109ea1) (shrR64Effect 0x109ea1 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x109ea1 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x109ea1 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x109ea5 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x109ea5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ea5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ea5 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109ea5 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109ea5 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x109eaa [0x48, 0x8D, 0x44, 0x24, 0x08] (fun s => s.RIP = 0x109eaa) (leaR64Effect 0x109eaa 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x109eaa 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x109eaa 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x109eaf [0x31, 0xC9] (fun s => s.RIP = 0x109eaf) (xorR32R32Effect 0x109eaf 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109eaf 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x109eaf 0xc9 (by decide)) pre_rip
  have f24 : InstrSpec 0x109eb1 [0x31, 0xD2] (fun s => s.RIP = 0x109eb1) (xorR32R32Effect 0x109eb1 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109eb1 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x109eb1 0xd2 (by decide)) pre_rip
  have f25 : InstrSpec 0x109eb3 [0x48, 0x2B, 0x54, 0x24, 0x08] (LoadPre 0x109eb3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109eb3 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109eb3 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x109eb3 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x109eb3 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x109eb8 [0x48, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x109eb8) (sarR64Effect 0x109eb8 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (sarR64Effect_footprint 0x109eb8 4 2 63).toInstrSpec (sar_r64_imm8_effect_step 0x109eb8 0x48 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x109ebc [0x48, 0xBE, 0xC5, 0x5F, 0xB7, 0x50, 0x19, 0x23, 0x51, 0x45] (fun s => s.RIP = 0x109ebc) (movR64Imm64Effect 0x109ebc 6 0x4551231950b75fc5)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x109ebc 6 0x4551231950b75fc5).toInstrSpec (mov_r64_imm64_effect_step 0x109ebc 0x48 0xbe (by decide) (by decide) 0x4551231950b75fc5) pre_rip
  have f28 : InstrSpec 0x109ec6 [0x4C, 0x01, 0xE6] (fun s => s.RIP = 0x109ec6) (addR64R64Effect 0x109ec6 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109ec6 6 12).toInstrSpec (add_r64_r64_effect_step 0x109ec6 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x109ec9 [0x48, 0x01, 0xD6] (fun s => s.RIP = 0x109ec9) (addR64R64Effect 0x109ec9 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109ec9 6 2).toInstrSpec (add_r64_r64_effect_step 0x109ec9 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x109ecc [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x109ecc) (movR64R64Effect 0x109ecc 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x109ecc 2 12).toInstrSpec (mov_r64_r64_effect_step 0x109ecc 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x109ecf [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x109ecf) (notR64Effect 0x109ecf 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x109ecf 2).toInstrSpec (not_r64_effect_step 0x109ecf 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x109ed2 [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x109ed2) (orR64R64Effect 0x109ed2 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109ed2 2 6).toInstrSpec (or_r64_r64_effect_step 0x109ed2 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x109ed5 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x109ed5) (shrR64Effect 0x109ed5 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x109ed5 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x109ed5 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x109ed9 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x109ed9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ed9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ed9 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109ed9 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109ed9 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x109ede [0x31, 0xD2] (fun s => s.RIP = 0x109ede) (xorR32R32Effect 0x109ede 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109ede 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x109ede 0xd2 (by decide)) pre_rip
  have f36 : InstrSpec 0x109ee0 [0x48, 0x2B, 0x54, 0x24, 0x08] (LoadPre 0x109ee0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ee0 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109ee0 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x109ee0 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x109ee0 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x109ee5 [0x48, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x109ee5) (sarR64Effect 0x109ee5 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (sarR64Effect_footprint 0x109ee5 4 2 63).toInstrSpec (sar_r64_imm8_effect_step 0x109ee5 0x48 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x109ee9 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x109ee9) (movR64R64Effect 0x109ee9 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x109ee9 6 15).toInstrSpec (mov_r64_r64_effect_step 0x109ee9 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x109eec [0x48, 0xF7, 0xD6] (fun s => s.RIP = 0x109eec) (notR64Effect 0x109eec 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR64Effect_footprint 0x109eec 6).toInstrSpec (not_r64_effect_step 0x109eec 0x48 0xd6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 85), (1, 93), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ea5) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 85), (1, 93), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eaa) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(1, 93), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eaf) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(1, 97), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eb1) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(1, 97), (2, 99), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eb3) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f25 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(1, 97), (2, 101), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eb8) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(1, 97), (2, 103), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ebc) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(1, 97), (2, 103), (3, 65), (4, 63), (5, 5), (6, 105), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ec6) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f28 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(1, 97), (2, 103), (3, 65), (4, 63), (5, 5), (6, 107), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ec9) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f29 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(1, 97), (2, 103), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ecc) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f30 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(1, 97), (2, 111), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ecf) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f31 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(1, 97), (2, 113), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ed2) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f32 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(1, 97), (2, 115), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ed5) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f33 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(1, 97), (2, 117), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ed9) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.exec (n := 119) (ρ' := [(1, 97), (2, 117), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ede) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f35 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(1, 97), (2, 120), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ee0) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f36 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(1, 97), (2, 122), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ee5) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f37 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(1, 97), (2, 124), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ee9) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f38 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(1, 97), (2, 124), (3, 65), (4, 63), (5, 5), (6, 126), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eec) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f39 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(1, 97), (2, 124), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eef) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109e60_2 code

theorem rest_l109e60 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109e60 bytes_l109e60) (entryMap (live .l109e60))
      58 0x109e60 bytes_l109e60 b_l109e60 := by
  have f0 : InstrSpec 0x109e60 [0x41, 0x57] (PushPre 0x109e60 2) (pushR64Effect 0x109e60 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109e60 2 15).toInstrSpec (push_r64_rex_effect_step 0x109e60 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x109e62 [0x41, 0x56] (PushPre 0x109e62 2) (pushR64Effect 0x109e62 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109e62 2 14).toInstrSpec (push_r64_rex_effect_step 0x109e62 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x109e64 [0x41, 0x55] (PushPre 0x109e64 2) (pushR64Effect 0x109e64 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109e64 2 13).toInstrSpec (push_r64_rex_effect_step 0x109e64 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x109e66 [0x41, 0x54] (PushPre 0x109e66 2) (pushR64Effect 0x109e66 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109e66 2 12).toInstrSpec (push_r64_rex_effect_step 0x109e66 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x109e68 [0x53] (PushPre 0x109e68 1) (pushR64Effect 0x109e68 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109e68 1 3).toInstrSpec (push_r64_effect_step 0x109e68 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x109e69 [0x48, 0x83, 0xEC, 0x10] (fun s => s.RIP = 0x109e69) (subR64Imm8Effect 0x109e69 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x109e69 4 0x10).toInstrSpec (sub_r64_imm8_effect_step 0x109e69 0x48 0xec 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x109e6d [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x109e6d) (movR64R64Effect 0x109e6d 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x109e6d 3 7).toInstrSpec (mov_r64_r64_effect_step 0x109e6d 0x48 0xfb (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x109e70 [0x4C, 0x8B, 0x36] (LoadPre 0x109e70 (fun s => AddrMode.addr (.base 6 .none) s (0x109e70 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109e70 14 (.base 6 .none))
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x109e70 14 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x109e70 0x4c (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x109e73 [0x4C, 0x8B, 0x7E, 0x08] (LoadPre 0x109e73 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109e73 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e73 15 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x109e73 15 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109e73 0x4c (by decide) 7 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x109e77 [0x49, 0x0F, 0xCE] (fun s => s.RIP = 0x109e77) (bswapR64Effect 0x109e77 3 14)
      [.gpr 14] [] [.reg 14, .rip] :=
    (bswapR64Effect_footprint 0x109e77 3 14).toInstrSpec (bswap_r64_effect_step 0x109e77 0x49 (by decide) 0xce (by decide)) pre_rip
  have f10 : InstrSpec 0x109e7a [0x49, 0x0F, 0xCF] (fun s => s.RIP = 0x109e7a) (bswapR64Effect 0x109e7a 3 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (bswapR64Effect_footprint 0x109e7a 3 15).toInstrSpec (bswap_r64_effect_step 0x109e7a 0x49 (by decide) 0xcf (by decide)) pre_rip
  have f11 : InstrSpec 0x109e7d [0x4C, 0x8B, 0x66, 0x10] (LoadPre 0x109e7d (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x109e7d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e7d 12 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x109e7d 12 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x109e7d 0x4c (by decide) 4 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x109e81 [0x49, 0x0F, 0xCC] (fun s => s.RIP = 0x109e81) (bswapR64Effect 0x109e81 3 12)
      [.gpr 12] [] [.reg 12, .rip] :=
    (bswapR64Effect_footprint 0x109e81 3 12).toInstrSpec (bswap_r64_effect_step 0x109e81 0x49 (by decide) 0xcc (by decide)) pre_rip
  have f13 : InstrSpec 0x109e84 [0x4C, 0x8B, 0x6E, 0x18] (LoadPre 0x109e84 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x109e84 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e84 13 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x109e84 13 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x109e84 0x4c (by decide) 5 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x109e88 [0x49, 0x0F, 0xCD] (fun s => s.RIP = 0x109e88) (bswapR64Effect 0x109e88 3 13)
      [.gpr 13] [] [.reg 13, .rip] :=
    (bswapR64Effect_footprint 0x109e88 3 13).toInstrSpec (bswap_r64_effect_step 0x109e88 0x49 (by decide) 0xcd (by decide)) pre_rip
  have f15 : InstrSpec 0x109e8b [0x48, 0xB8, 0xBF, 0xBE, 0xC9, 0x2F, 0x73, 0xA1, 0x2D, 0x40] (fun s => s.RIP = 0x109e8b) (movR64Imm64Effect 0x109e8b 0 0x402da1732fc9bebf)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x109e8b 0 0x402da1732fc9bebf).toInstrSpec (mov_r64_imm64_effect_step 0x109e8b 0x48 0xb8 (by decide) (by decide) 0x402da1732fc9bebf) pre_rip
  have f16 : InstrSpec 0x109e95 [0x4C, 0x01, 0xE8] (fun s => s.RIP = 0x109e95) (addR64R64Effect 0x109e95 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109e95 0 13).toInstrSpec (add_r64_r64_effect_step 0x109e95 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x109e98 [0x4C, 0x89, 0xE9] (fun s => s.RIP = 0x109e98) (movR64R64Effect 0x109e98 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x109e98 1 13).toInstrSpec (mov_r64_r64_effect_step 0x109e98 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x109e9b [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x109e9b) (notR64Effect 0x109e9b 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x109e9b 1).toInstrSpec (not_r64_effect_step 0x109e9b 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x109e9e [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x109e9e) (orR64R64Effect 0x109e9e 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109e9e 1 0).toInstrSpec (or_r64_r64_effect_step 0x109e9e 0x48 0xc1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e62) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e64) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e66) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e68) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e69) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e6d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e70) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e73) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e77) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e7a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e7d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 75), (13, 13), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e81) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 13), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e84) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 79), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e88) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e8b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e95) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e98) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 85), (1, 87), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e9b) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 85), (1, 89), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e9e) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 85), (1, 91), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ea1) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109e60_1 code

theorem block_l109e60 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109e60 :=
  Rest.liftedBlock (rest_l109e60 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109e60 x hx)

theorem rest_l109f32 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109f32 bytes_l109f32) (entryMap (live .l109f32))
      13 0x109f32 bytes_l109f32 b_l109f32 := by
  have f0 : InstrSpec 0x109f32 [0x4C, 0x89, 0x2B] (StorePre 0x109f32 3 (fun s => AddrMode.addr (.base 3 .none) s (0x109f32 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x109f32 13 (.base 3 .none))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x109f32 13 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x109f32 0x4c (by decide) 5 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x109f35 [0x4C, 0x89, 0x63, 0x08] (StorePre 0x109f35 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x109f35 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109f35 12 (.base 3 (.d8 0x8)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x109f35 12 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109f35 0x4c (by decide) 4 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x109f39 [0x4C, 0x89, 0x7B, 0x10] (StorePre 0x109f39 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x109f39 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109f39 15 (.base 3 (.d8 0x10)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x109f39 15 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x109f39 0x4c (by decide) 7 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x109f3d [0x4C, 0x89, 0x73, 0x18] (StorePre 0x109f3d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x109f3d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109f3d 14 (.base 3 (.d8 0x18)))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x109f3d 14 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x109f3d 0x4c (by decide) 6 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x109f41 [0x88, 0x43, 0x20] (StorePre 0x109f41 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x109f41 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109f41 3 0 (.base 3 (.d8 0x20)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x109f41 3 0 (.base 3 (.d8 0x20))).toInstrSpec (mov_m8_r8_effect_step 0x109f41 0 (by decide) (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x109f44 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x109f44) (movR64R64Effect 0x109f44 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109f44 0 3).toInstrSpec (mov_r64_r64_effect_step 0x109f44 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x109f47 [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x109f47) (addR64Imm8Effect 0x109f47 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x109f47 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x109f47 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x109f4b [0x5B] (PopPre 0x109f4b) (popR64Effect 0x109f4b 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109f4b 1 3).toInstrSpec (pop_r64_effect_step 0x109f4b 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x109f4c [0x41, 0x5C] (PopPre 0x109f4c) (popR64Effect 0x109f4c 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109f4c 2 12).toInstrSpec (pop_r64_rex_effect_step 0x109f4c 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x109f4e [0x41, 0x5D] (PopPre 0x109f4e) (popR64Effect 0x109f4e 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109f4e 2 13).toInstrSpec (pop_r64_rex_effect_step 0x109f4e 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x109f50 [0x41, 0x5E] (PopPre 0x109f50) (popR64Effect 0x109f50 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109f50 2 14).toInstrSpec (pop_r64_rex_effect_step 0x109f50 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x109f52 [0x41, 0x5F] (PopPre 0x109f52) (popR64Effect 0x109f52 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109f52 2 15).toInstrSpec (pop_r64_rex_effect_step 0x109f52 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f12 : InstrSpec 0x109f54 [0xC3] (RetPre 0x109f54) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x109f54).toInstrSpec (ret_effect_step 0x109f54) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f35) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f39) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f3d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f41) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f44) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f47) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f4b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 62), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f4c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 62), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f4e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 70) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 62), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 68), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f50) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 62), (4, 72), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 68), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f52) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 75) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 76) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 62), (4, 75), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 68), (14, 71), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f54) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 78) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 79) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 62), (4, 78), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 68), (14, 71), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) f12 (by decide) rfl rfl rfl (by decide)

theorem block_l109f32 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109f32 :=
  Rest.liftedBlock (rest_l109f32 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109f32 x hx)

theorem rest_l109f60 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109f60 bytes_l109f60) (entryMap (live .l109f60))
      1 0x109f60 bytes_l109f60 b_l109f60 := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x109f60 0xfffffa5b (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l109f60 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109f60 :=
  Rest.liftedBlock (rest_l109f60 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109f60 x hx)

theorem rest_l109f70 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109f70 bytes_l109f70) (entryMap (live .l109f70))
      1 0x109f70 bytes_l109f70 b_l109f70 := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x109f70 0xfffffa4b (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l109f70 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109f70 :=
  Rest.liftedBlock (rest_l109f70 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109f70 x hx)

theorem rest_l109f80_2 [Bindings] (code : CodeMap) :
    Rest (n := 127) code lifted (codeRange 0x109f80 bytes_l109f80) [(1, 125), (2, 120), (3, 3), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      16 0x10a014 bytes_l109f80_2 b_l109f80_2 := by
  have f40 : InstrSpec 0x10a014 [0x48, 0x09, 0xD1] (fun s => s.RIP = 0x10a014) (orR64R64Effect 0x10a014 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a014 1 2).toInstrSpec (or_r64_r64_effect_step 0x10a014 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x10a017 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x10a017) (shrR64Effect 0x10a017 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a017 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x10a017 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x10a01b [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x10a01b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a01b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a01b 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a01b 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10a01b 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f43 : InstrSpec 0x10a020 [0x48, 0x8B, 0x5C, 0x24, 0x08] (LoadPre 0x10a020 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a020 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a020 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x10a020 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10a020 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f44 : InstrSpec 0x10a025 [0x4C, 0x8B, 0x7E, 0x18] (LoadPre 0x10a025 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10a025 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a025 15 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10a025 15 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10a025 0x4c (by decide) 7 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f45 : InstrSpec 0x10a029 [0x48, 0xFF, 0xCB] (fun s => s.RIP = 0x10a029) (decR64Effect 0x10a029 3)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (decR64Effect_footprint 0x10a029 3).toInstrSpec (dec_r64_effect_step 0x10a029 0x48 0xcb (by decide) (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x10a02c [0x48, 0xC1, 0xEB, 0x3F] (fun s => s.RIP = 0x10a02c) (shrR64Effect 0x10a02c 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a02c 4 3 63).toInstrSpec (shr_r64_imm8_effect_step 0x10a02c 0x48 0xeb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x10a030 [0x4C, 0x01, 0xFB] (fun s => s.RIP = 0x10a030) (addR64R64Effect 0x10a030 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10a030 3 15).toInstrSpec (add_r64_r64_effect_step 0x10a030 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x10a033 [0x4C, 0x89, 0xF9] (fun s => s.RIP = 0x10a033) (movR64R64Effect 0x10a033 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10a033 1 15).toInstrSpec (mov_r64_r64_effect_step 0x10a033 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x10a036 [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x10a036) (notR64Effect 0x10a036 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x10a036 1).toInstrSpec (not_r64_effect_step 0x10a036 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x10a039 [0x48, 0x09, 0xD9] (fun s => s.RIP = 0x10a039) (orR64R64Effect 0x10a039 1 3)
      [.gpr 1, .gpr 3] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a039 1 3).toInstrSpec (or_r64_r64_effect_step 0x10a039 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x10a03c [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x10a03c) (shrR64Effect 0x10a03c 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a03c 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x10a03c 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x10a040 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x10a040 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a040 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a040 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a040 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10a040 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f53 : InstrSpec 0x10a045 [0x48, 0x2B, 0x7C, 0x24, 0x08] (LoadPre 0x10a045 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a045 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10a045 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 7, .gpr 4] [] [.reg 7, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10a045 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x10a045 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f54 : InstrSpec 0x10a04a [0x48, 0xC1, 0xEF, 0x3F] (fun s => s.RIP = 0x10a04a) (shrR64Effect 0x10a04a 4 7 63)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a04a 4 7 63).toInstrSpec (shr_r64_imm8_effect_step 0x10a04a 0x48 0xef 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x10a04e [0xE8, 0xFD, 0xDC, 0x01, 0x00] (PushPre 0x10a04e 5) (callEffect (fun _ => 0x127d50) 0x10a053)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a04e 0x127d50 0x10a053).toInstrSpec (call_rel32_effect_step 0x10a04e 0x1dcfd (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f40 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(1, 127), (2, 120), (3, 3), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a017) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f41 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(1, 129), (2, 120), (3, 3), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a01b) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.exec (n := 131) (ρ' := [(1, 129), (2, 120), (3, 3), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a020) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f43 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(1, 129), (2, 120), (3, 132), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a025) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f44 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(1, 129), (2, 120), (3, 132), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a029) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f45 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(1, 129), (2, 120), (3, 136), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a02c) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f46 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(1, 129), (2, 120), (3, 138), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a030) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f47 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(1, 129), (2, 120), (3, 140), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a033) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f48 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(1, 142), (2, 120), (3, 140), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a036) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f49 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(1, 144), (2, 120), (3, 140), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a039) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f50 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(1, 146), (2, 120), (3, 140), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a03c) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f51 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(1, 148), (2, 120), (3, 140), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a040) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.exec (n := 150) (ρ' := [(1, 148), (2, 120), (3, 140), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a045) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f53 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(1, 148), (2, 120), (3, 140), (4, 65), (5, 114), (6, 6), (7, 151), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a04a) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f54 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(1, 148), (2, 120), (3, 140), (4, 65), (5, 114), (6, 6), (7, 153), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a04e) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f55 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(1, 148), (2, 120), (3, 140), (4, 155), (5, 114), (6, 6), (7, 153), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f55 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 157) (by decide) (by decide) rfl rfl

theorem rest_l109f80_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x109f80 bytes_l109f80) [(1, 87), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      36 0x109fc6 bytes_l109f80_1 b_l109f80_1 := by
  have f20 : InstrSpec 0x109fc6 [0x4C, 0x8B, 0x66, 0x08] (LoadPre 0x109fc6 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109fc6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109fc6 12 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x109fc6 12 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109fc6 0x4c (by decide) 4 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x109fca [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x109fca) (sarR64Effect 0x109fca 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x109fca 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x109fca 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x109fce [0x49, 0xBD, 0xC5, 0x5F, 0xB7, 0x50, 0x19, 0x23, 0x51, 0x45] (fun s => s.RIP = 0x109fce) (movR64Imm64Effect 0x109fce 13 0x4551231950b75fc5)
      [] [] [.reg 13, .rip] :=
    (movR64Imm64Effect_footprint 0x109fce 13 0x4551231950b75fc5).toInstrSpec (mov_r64_imm64_effect_step 0x109fce 0x49 0xbd (by decide) (by decide) 0x4551231950b75fc5) pre_rip
  have f23 : InstrSpec 0x109fd8 [0x4D, 0x01, 0xE5] (fun s => s.RIP = 0x109fd8) (addR64R64Effect 0x109fd8 13 12)
      [.gpr 13, .gpr 12] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109fd8 13 12).toInstrSpec (add_r64_r64_effect_step 0x109fd8 0x4d 0xe5 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x109fdb [0x49, 0x01, 0xCD] (fun s => s.RIP = 0x109fdb) (addR64R64Effect 0x109fdb 13 1)
      [.gpr 13, .gpr 1] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109fdb 13 1).toInstrSpec (add_r64_r64_effect_step 0x109fdb 0x49 0xcd (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x109fde [0x4C, 0x89, 0xE1] (fun s => s.RIP = 0x109fde) (movR64R64Effect 0x109fde 1 12)
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x109fde 1 12).toInstrSpec (mov_r64_r64_effect_step 0x109fde 0x4c 0xe1 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x109fe1 [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x109fe1) (notR64Effect 0x109fe1 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x109fe1 1).toInstrSpec (not_r64_effect_step 0x109fe1 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x109fe4 [0x4C, 0x09, 0xE9] (fun s => s.RIP = 0x109fe4) (orR64R64Effect 0x109fe4 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109fe4 1 13).toInstrSpec (or_r64_r64_effect_step 0x109fe4 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x109fe7 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x109fe7) (shrR64Effect 0x109fe7 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x109fe7 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x109fe7 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x109feb [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x109feb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109feb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109feb 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109feb 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109feb 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x109ff0 [0x31, 0xC9] (fun s => s.RIP = 0x109ff0) (xorR32R32Effect 0x109ff0 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109ff0 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x109ff0 0xc9 (by decide)) pre_rip
  have f31 : InstrSpec 0x109ff2 [0x48, 0x2B, 0x4C, 0x24, 0x08] (LoadPre 0x109ff2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ff2 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109ff2 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x109ff2 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x109ff2 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x109ff7 [0x31, 0xFF] (fun s => s.RIP = 0x109ff7) (xorR32R32Effect 0x109ff7 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109ff7 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x109ff7 0xff (by decide)) pre_rip
  have f33 : InstrSpec 0x109ff9 [0x48, 0x8B, 0x6E, 0x10] (LoadPre 0x109ff9 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x109ff9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109ff9 5 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x109ff9 5 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x109ff9 0x48 (by decide) 5 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f34 : InstrSpec 0x109ffd [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x109ffd) (sarR64Effect 0x109ffd 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x109ffd 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x109ffd 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x10a001 [0x48, 0x8D, 0x14, 0x29] (fun s => s.RIP = 0x10a001) (leaR64Effect 0x10a001 2 (.sib 1 (some 5) 0 .none))
      [.gpr 1, .gpr 5] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x10a001 2 (.sib 1 (some 5) 0 .none)).toInstrSpec (lea_r64_effect_step 0x10a001 0x48 (by decide) 2 (.sib 1 (some 5) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x10a005 [0x48, 0x83, 0xC2, 0x02] (fun s => s.RIP = 0x10a005) (addR64Imm8Effect 0x10a005 2 0x2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10a005 2 0x2).toInstrSpec (add_r64_imm8_effect_step 0x10a005 0x48 0xc2 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x10a009 [0x48, 0x89, 0x54, 0x24, 0x10] (StorePre 0x10a009 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a009 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a009 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a009 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10a009 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x10a00e [0x48, 0x89, 0xE9] (fun s => s.RIP = 0x10a00e) (movR64R64Effect 0x10a00e 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10a00e 1 5).toInstrSpec (mov_r64_r64_effect_step 0x10a00e 0x48 0xe9 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10a011 [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x10a011) (notR64Effect 0x10a011 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x10a011 1).toInstrSpec (not_r64_effect_step 0x10a011 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f20 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(1, 87), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fca) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(1, 91), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fce) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f22 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(1, 91), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 93), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fd8) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f23 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(1, 91), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 95), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fdb) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f24 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(1, 91), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fde) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f25 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(1, 99), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fe1) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(1, 101), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fe4) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f27 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(1, 103), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fe7) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f28 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(1, 105), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109feb) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(1, 105), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ff0) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f30 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(1, 108), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ff2) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f31 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(1, 110), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ff7) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f32 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(1, 110), (3, 3), (4, 65), (5, 5), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ff9) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f33 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(1, 110), (3, 3), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ffd) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f34 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(1, 116), (3, 3), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a001) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f35 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(1, 116), (2, 118), (3, 3), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a005) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f36 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(1, 116), (2, 120), (3, 3), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a009) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.exec (n := 122) (ρ' := [(1, 116), (2, 120), (3, 3), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a00e) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f38 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(1, 123), (2, 120), (3, 3), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a011) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f39 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(1, 125), (2, 120), (3, 3), (4, 65), (5, 114), (6, 6), (7, 112), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a014) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109f80_2 code

theorem rest_l109f80 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109f80 bytes_l109f80) (entryMap (live .l109f80))
      56 0x109f80 bytes_l109f80 b_l109f80 := by
  have f0 : InstrSpec 0x109f80 [0x55] (PushPre 0x109f80 1) (pushR64Effect 0x109f80 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109f80 1 5).toInstrSpec (push_r64_effect_step 0x109f80 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x109f81 [0x41, 0x57] (PushPre 0x109f81 2) (pushR64Effect 0x109f81 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109f81 2 15).toInstrSpec (push_r64_rex_effect_step 0x109f81 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x109f83 [0x41, 0x56] (PushPre 0x109f83 2) (pushR64Effect 0x109f83 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109f83 2 14).toInstrSpec (push_r64_rex_effect_step 0x109f83 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x109f85 [0x41, 0x55] (PushPre 0x109f85 2) (pushR64Effect 0x109f85 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109f85 2 13).toInstrSpec (push_r64_rex_effect_step 0x109f85 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x109f87 [0x41, 0x54] (PushPre 0x109f87 2) (pushR64Effect 0x109f87 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109f87 2 12).toInstrSpec (push_r64_rex_effect_step 0x109f87 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x109f89 [0x53] (PushPre 0x109f89 1) (pushR64Effect 0x109f89 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109f89 1 3).toInstrSpec (push_r64_effect_step 0x109f89 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x109f8a [0x48, 0x83, 0xEC, 0x28] (fun s => s.RIP = 0x109f8a) (subR64Imm8Effect 0x109f8a 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x109f8a 4 0x28).toInstrSpec (sub_r64_imm8_effect_step 0x109f8a 0x48 0xec 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x109f8e [0x48, 0x89, 0x7C, 0x24, 0x20] (StorePre 0x109f8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109f8e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109f8e 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109f8e 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x109f8e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x109f93 [0x4C, 0x8B, 0x36] (LoadPre 0x109f93 (fun s => AddrMode.addr (.base 6 .none) s (0x109f93 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109f93 14 (.base 6 .none))
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x109f93 14 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x109f93 0x4c (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x109f96 [0x48, 0xB9, 0xBF, 0xBE, 0xC9, 0x2F, 0x73, 0xA1, 0x2D, 0x40] (fun s => s.RIP = 0x109f96) (movR64Imm64Effect 0x109f96 1 0x402da1732fc9bebf)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x109f96 1 0x402da1732fc9bebf).toInstrSpec (mov_r64_imm64_effect_step 0x109f96 0x48 0xb9 (by decide) (by decide) 0x402da1732fc9bebf) pre_rip
  have f10 : InstrSpec 0x109fa0 [0x4C, 0x01, 0xF1] (fun s => s.RIP = 0x109fa0) (addR64R64Effect 0x109fa0 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109fa0 1 14).toInstrSpec (add_r64_r64_effect_step 0x109fa0 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x109fa3 [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x109fa3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109fa3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109fa3 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109fa3 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x109fa3 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x109fa8 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x109fa8) (movR64R64Effect 0x109fa8 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109fa8 0 14).toInstrSpec (mov_r64_r64_effect_step 0x109fa8 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x109fab [0x48, 0xF7, 0xD0] (fun s => s.RIP = 0x109fab) (notR64Effect 0x109fab 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR64Effect_footprint 0x109fab 0).toInstrSpec (not_r64_effect_step 0x109fab 0x48 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x109fae [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x109fae) (orR64R64Effect 0x109fae 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109fae 0 1).toInstrSpec (or_r64_r64_effect_step 0x109fae 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x109fb1 [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x109fb1) (shrR64Effect 0x109fb1 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x109fb1 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x109fb1 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x109fb5 [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x109fb5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109fb5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109fb5 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109fb5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109fb5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x109fba [0x48, 0x8D, 0x44, 0x24, 0x08] (fun s => s.RIP = 0x109fba) (leaR64Effect 0x109fba 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x109fba 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x109fba 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x109fbf [0x31, 0xC9] (fun s => s.RIP = 0x109fbf) (xorR32R32Effect 0x109fbf 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109fbf 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x109fbf 0xc9 (by decide)) pre_rip
  have f19 : InstrSpec 0x109fc1 [0x48, 0x2B, 0x4C, 0x24, 0x08] (LoadPre 0x109fc1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109fc1 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109fc1 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x109fc1 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x109fc1 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f81) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f83) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f85) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f87) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f89) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f8a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f8e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f93) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f96) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(1, 70), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fa0) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(1, 72), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fa3) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(1, 72), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fa8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 72), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fab) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 72), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fae) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 72), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fb1) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 72), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fb5) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 81), (1, 72), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fba) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(1, 72), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fbf) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(1, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fc1) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(1, 87), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109fc6) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109f80_1 code

theorem block_l109f80 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109f80 :=
  Rest.liftedBlock (rest_l109f80 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109f80 x hx)

theorem rest_l10a053 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a053 bytes_l10a053) (entryMap (live .l10a053))
      4 0x10a053 bytes_l10a053 b_l10a053 := by
  have f0 : InstrSpec 0x10a053 [0xF6, 0xD0] (fun s => s.RIP = 0x10a053) (notR8Effect 0x10a053 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR8Effect_footprint 0x10a053 2 0).toInstrSpec (not_r8_effect_step 0x10a053 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10a055 [0x24, 0x01] (fun s => s.RIP = 0x10a055) (andAlImm8Effect 0x10a055 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x10a055 0x1).toInstrSpec (and_al_imm8_effect_step 0x10a055 0x1) pre_rip
  have f2 : InstrSpec 0x10a057 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x10a057) (movzxR32R8Effect 0x10a057 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x10a057 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x10a057 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10a05a [0xE8, 0xF1, 0xDC, 0x01, 0x00] (PushPre 0x10a05a 5) (callEffect (fun _ => 0x127d50) 0x10a05f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a05a 0x127d50 0x10a05f).toInstrSpec (call_rel32_effect_step 0x10a05a 0x1dcf1 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a055) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a057) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a05a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10a053 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a053 :=
  Rest.liftedBlock (rest_l10a053 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a053 x hx)

theorem rest_l10a05f_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x10a05f bytes_l10a05f) [(0, 77), (1, 67), (2, 2), (3, 85), (4, 86), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 61), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x10a0a8 bytes_l10a05f_1 b_l10a05f_1 := by
  have f20 : InstrSpec 0x10a0a8 [0x41, 0x5C] (PopPre 0x10a0a8) (popR64Effect 0x10a0a8 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a0a8 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10a0a8 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f21 : InstrSpec 0x10a0aa [0x41, 0x5D] (PopPre 0x10a0aa) (popR64Effect 0x10a0aa 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a0aa 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10a0aa 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f22 : InstrSpec 0x10a0ac [0x41, 0x5E] (PopPre 0x10a0ac) (popR64Effect 0x10a0ac 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a0ac 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10a0ac 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f23 : InstrSpec 0x10a0ae [0x41, 0x5F] (PopPre 0x10a0ae) (popR64Effect 0x10a0ae 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a0ae 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10a0ae 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f24 : InstrSpec 0x10a0b0 [0x5D] (PopPre 0x10a0b0) (popR64Effect 0x10a0b0 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a0b0 1 5).toInstrSpec (pop_r64_effect_step 0x10a0b0 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f25 : InstrSpec 0x10a0b1 [0xC3] (RetPre 0x10a0b1) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10a0b1).toInstrSpec (ret_effect_step 0x10a0b1) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f20 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 89) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 90) (ρ' := [(0, 77), (1, 67), (2, 2), (3, 85), (4, 89), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 88), (13, 13), (14, 61), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0aa) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f21 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 92) f21 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 93) (ρ' := [(0, 77), (1, 67), (2, 2), (3, 85), (4, 92), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 88), (13, 91), (14, 61), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0ac) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f22 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 95) f22 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 96) (ρ' := [(0, 77), (1, 67), (2, 2), (3, 85), (4, 95), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 88), (13, 91), (14, 94), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0ae) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 98) f23 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 99) (ρ' := [(0, 77), (1, 67), (2, 2), (3, 85), (4, 98), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 88), (13, 91), (14, 94), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0b0) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f24 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 101) f24 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 102) (ρ' := [(0, 77), (1, 67), (2, 2), (3, 85), (4, 101), (5, 100), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 88), (13, 91), (14, 94), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0b1) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 104) f25 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 105) (ρ' := [(0, 77), (1, 67), (2, 2), (3, 85), (4, 104), (5, 100), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 88), (13, 91), (14, 94), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) f25 (by decide) rfl rfl rfl (by decide)

theorem rest_l10a05f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a05f bytes_l10a05f) (entryMap (live .l10a05f))
      26 0x10a05f bytes_l10a05f b_l10a05f := by
  have f0 : InstrSpec 0x10a05f [0x88, 0x44, 0x24, 0x07] (StorePre 0x10a05f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10a05f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a05f 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a05f 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x10a05f 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10a063 [0x48, 0x8D, 0x44, 0x24, 0x07] (fun s => s.RIP = 0x10a063) (leaR64Effect 0x10a063 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x10a063 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x10a063 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10a068 [0x0F, 0xB6, 0x44, 0x24, 0x07] (LoadPre 0x10a068 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10a068 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a068 5 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a068 5 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x10a068 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10a06d [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x10a06d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10a06d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a06d 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10a06d 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10a06d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10a072 [0x84, 0xC0] (fun s => s.RIP = 0x10a072) (testR8R8Effect 0x10a072 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10a072 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x10a072 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10a074 [0x4C, 0x0F, 0x45, 0xF1] (fun s => s.RIP = 0x10a074) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a074 4 14 1))
      [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 14, .rip] :=
    (cmovR64R64Effect_footprint 0x10a074 4 14 1 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10a074 5 0x4c (by decide) 0xf1 (by decide) c)) pre_rip
  have f6 : InstrSpec 0x10a078 [0x84, 0xC0] (fun s => s.RIP = 0x10a078) (testR8R8Effect 0x10a078 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10a078 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x10a078 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10a07a [0x4D, 0x0F, 0x45, 0xE5] (fun s => s.RIP = 0x10a07a) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a07a 4 12 13))
      [.gpr 12, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 12, .rip] :=
    (cmovR64R64Effect_footprint 0x10a07a 4 12 13 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10a07a 5 0x4d (by decide) 0xe5 (by decide) c)) pre_rip
  have f8 : InstrSpec 0x10a07e [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x10a07e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a07e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a07e 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10a07e 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10a07e 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10a083 [0x84, 0xC0] (fun s => s.RIP = 0x10a083) (testR8R8Effect 0x10a083 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10a083 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x10a083 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10a085 [0x48, 0x0F, 0x45, 0xE9] (fun s => s.RIP = 0x10a085) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a085 4 5 1))
      [.gpr 5, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 5, .rip] :=
    (cmovR64R64Effect_footprint 0x10a085 4 5 1 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10a085 5 0x48 (by decide) 0xe9 (by decide) c)) pre_rip
  have f11 : InstrSpec 0x10a089 [0x84, 0xC0] (fun s => s.RIP = 0x10a089) (testR8R8Effect 0x10a089 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10a089 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x10a089 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10a08b [0x4C, 0x0F, 0x45, 0xFB] (fun s => s.RIP = 0x10a08b) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a08b 4 15 3))
      [.gpr 15, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 15, .rip] :=
    (cmovR64R64Effect_footprint 0x10a08b 4 15 3 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10a08b 5 0x4c (by decide) 0xfb (by decide) c)) pre_rip
  have f13 : InstrSpec 0x10a08f [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x10a08f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10a08f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a08f 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10a08f 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10a08f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10a094 [0x4C, 0x89, 0x30] (StorePre 0x10a094 3 (fun s => AddrMode.addr (.base 0 .none) s (0x10a094 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10a094 14 (.base 0 .none))
      [.gpr 14, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a094 14 (.base 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10a094 0x4c (by decide) 6 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x10a097 [0x4C, 0x89, 0x60, 0x08] (StorePre 0x10a097 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x10a097 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a097 12 (.base 0 (.d8 0x8)))
      [.gpr 12, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a097 12 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10a097 0x4c (by decide) 4 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x10a09b [0x48, 0x89, 0x68, 0x10] (StorePre 0x10a09b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x10a09b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a09b 5 (.base 0 (.d8 0x10)))
      [.gpr 5, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a09b 5 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10a09b 0x48 (by decide) 5 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x10a09f [0x4C, 0x89, 0x78, 0x18] (StorePre 0x10a09f 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x10a09f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a09f 15 (.base 0 (.d8 0x18)))
      [.gpr 15, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a09f 15 (.base 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10a09f 0x4c (by decide) 7 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x10a0a3 [0x48, 0x83, 0xC4, 0x28] (fun s => s.RIP = 0x10a0a3) (addR64Imm8Effect 0x10a0a3 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10a0a3 4 0x28).toInstrSpec (add_r64_imm8_effect_step 0x10a0a3 0x48 0xc4 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x10a0a7 [0x5B] (PopPre 0x10a0a7) (popR64Effect 0x10a0a7 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a0a7 1 3).toInstrSpec (pop_r64_effect_step 0x10a0a7 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a063) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a068) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a06d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a072) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a074) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a078) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a07a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 61), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a07e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 61), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a083) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 61), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a085) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 4), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 61), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a089) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 4), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 61), (15, 15), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a08b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 4), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 61), (15, 75), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a08f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 67), (2, 2), (3, 3), (4, 4), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 61), (15, 75), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a094) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (1, 67), (2, 2), (3, 3), (4, 4), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 61), (15, 75), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a097) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 77), (1, 67), (2, 2), (3, 3), (4, 4), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 61), (15, 75), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a09b) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 77), (1, 67), (2, 2), (3, 3), (4, 4), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 61), (15, 75), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a09f) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 77), (1, 67), (2, 2), (3, 3), (4, 4), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 61), (15, 75), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0a3) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 77), (1, 67), (2, 2), (3, 3), (4, 83), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 61), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0a7) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f19 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 77), (1, 67), (2, 2), (3, 85), (4, 86), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 61), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0a8) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a05f_1 code

theorem block_l10a05f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a05f :=
  Rest.liftedBlock (rest_l10a05f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a05f x hx)

theorem rest_l10a0c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a0c0 bytes_l10a0c0) (entryMap (live .l10a0c0))
      12 0x10a0c0 bytes_l10a0c0 b_l10a0c0 := by
  have f0 : InstrSpec 0x10a0c0 [0x41, 0x57] (PushPre 0x10a0c0 2) (pushR64Effect 0x10a0c0 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a0c0 2 15).toInstrSpec (push_r64_rex_effect_step 0x10a0c0 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10a0c2 [0x41, 0x56] (PushPre 0x10a0c2 2) (pushR64Effect 0x10a0c2 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a0c2 2 14).toInstrSpec (push_r64_rex_effect_step 0x10a0c2 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x10a0c4 [0x41, 0x55] (PushPre 0x10a0c4 2) (pushR64Effect 0x10a0c4 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a0c4 2 13).toInstrSpec (push_r64_rex_effect_step 0x10a0c4 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10a0c6 [0x41, 0x54] (PushPre 0x10a0c6 2) (pushR64Effect 0x10a0c6 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a0c6 2 12).toInstrSpec (push_r64_rex_effect_step 0x10a0c6 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10a0c8 [0x53] (PushPre 0x10a0c8 1) (pushR64Effect 0x10a0c8 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a0c8 1 3).toInstrSpec (push_r64_effect_step 0x10a0c8 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10a0c9 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x10a0c9) (subR64Imm8Effect 0x10a0c9 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10a0c9 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x10a0c9 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10a0cd [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x10a0cd) (movR64R64Effect 0x10a0cd 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10a0cd 3 7).toInstrSpec (mov_r64_r64_effect_step 0x10a0cd 0x48 0xfb (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10a0d0 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x10a0d0) (leaR64Effect 0x10a0d0 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10a0d0 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10a0d0 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10a0d5 [0x48, 0xB9, 0xC1, 0x4E, 0x77, 0xAA, 0x99, 0x00, 0xF2, 0xB4] (fun s => s.RIP = 0x10a0d5) (movR64Imm64Effect 0x10a0d5 1 0xb4f20099aa774ec1)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10a0d5 1 0xb4f20099aa774ec1).toInstrSpec (mov_r64_imm64_effect_step 0x10a0d5 0x48 0xb9 (by decide) (by decide) 0xb4f20099aa774ec1) pre_rip
  have f9 : InstrSpec 0x10a0df [0x48, 0xC7, 0xC2, 0xA0, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x10a0df) (movR64Imm32Effect 0x10a0df 2 0x2021a0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10a0df 2 0x2021a0).toInstrSpec (mov_r64_imm32_effect_step 0x10a0df 0x48 0xc2 (by decide) (by decide) (by decide) 0x2021a0) pre_rip
  have f10 : InstrSpec 0x10a0e6 [0x49, 0xC7, 0xC0, 0x80, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x10a0e6) (movR64Imm32Effect 0x10a0e6 8 0x202180)
      [] [] [.reg 8, .rip] :=
    (movR64Imm32Effect_footprint 0x10a0e6 8 0x202180).toInstrSpec (mov_r64_imm32_effect_step 0x10a0e6 0x49 0xc0 (by decide) (by decide) (by decide) 0x202180) pre_rip
  have f11 : InstrSpec 0x10a0ed [0xE8, 0x9E, 0xF3, 0xFF, 0xFF] (PushPre 0x10a0ed 5) (callEffect (fun _ => 0x109490) 0x10a0f2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a0ed 0x109490 0x10a0f2).toInstrSpec (call_rel32_effect_step 0x10a0ed 0xfffff39e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0c2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0c4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0c6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0c8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0c9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0cd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0d0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(3, 65), (4, 63), (5, 5), (6, 6), (7, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0d5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 69), (3, 65), (4, 63), (5, 5), (6, 6), (7, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0df) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 69), (2, 71), (3, 65), (4, 63), (5, 5), (6, 6), (7, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0e6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 69), (2, 71), (3, 65), (4, 63), (5, 5), (6, 6), (7, 67), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0ed) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 69), (2, 71), (3, 65), (4, 75), (5, 5), (6, 6), (7, 67), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109490) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l10a0c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a0c0 :=
  Rest.liftedBlock (rest_l10a0c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a0c0 x hx)

theorem rest_l10a0f2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a0f2 bytes_l10a0f2) (entryMap (live .l10a0f2))
      6 0x10a0f2 bytes_l10a0f2 b_l10a0f2 := by
  have f0 : InstrSpec 0x10a0f2 [0x4C, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x10a0f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a0f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a0f2 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x10a0f2 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10a0f2 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10a0f7 [0x4C, 0x8B, 0x7C, 0x24, 0x10] (LoadPre 0x10a0f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a0f7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a0f7 15 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10a0f7 15 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10a0f7 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10a0fc [0x4C, 0x8B, 0x64, 0x24, 0x18] (LoadPre 0x10a0fc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10a0fc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a0fc 12 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x10a0fc 12 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10a0fc 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10a101 [0x4C, 0x8B, 0x6C, 0x24, 0x20] (LoadPre 0x10a101 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10a101 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a101 13 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x10a101 13 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10a101 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10a106 [0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x10a106 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10a106 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10a106 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x10a106 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r32_m32_low_effect_step 0x10a106 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10a10a [0xE8, 0x41, 0xDC, 0x01, 0x00] (PushPre 0x10a10a 5) (callEffect (fun _ => 0x127d50) 0x10a10f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a10a 0x127d50 0x10a10f).toInstrSpec (call_rel32_effect_step 0x10a10a 0x1dc41 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0f7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0fc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a101) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a106) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a10a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l10a0f2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a0f2 :=
  Rest.liftedBlock (rest_l10a0f2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a0f2 x hx)

theorem rest_l10a10f_1 [Bindings] (code : CodeMap) :
    Rest (n := 86) code lifted (codeRange 0x10a10f bytes_l10a10f) [(0, 0), (1, 55), (2, 79), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]
      8 0x10a150 bytes_l10a10f_1 b_l10a10f_1 := by
  have f20 : InstrSpec 0x10a150 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10a150) (movR64R64Effect 0x10a150 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10a150 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10a150 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x10a153 [0x48, 0x83, 0xC4, 0x30] (fun s => s.RIP = 0x10a153) (addR64Imm8Effect 0x10a153 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10a153 4 0x30).toInstrSpec (add_r64_imm8_effect_step 0x10a153 0x48 0xc4 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10a157 [0x5B] (PopPre 0x10a157) (popR64Effect 0x10a157 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a157 1 3).toInstrSpec (pop_r64_effect_step 0x10a157 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f23 : InstrSpec 0x10a158 [0x41, 0x5C] (PopPre 0x10a158) (popR64Effect 0x10a158 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a158 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10a158 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f24 : InstrSpec 0x10a15a [0x41, 0x5D] (PopPre 0x10a15a) (popR64Effect 0x10a15a 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a15a 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10a15a 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f25 : InstrSpec 0x10a15c [0x41, 0x5E] (PopPre 0x10a15c) (popR64Effect 0x10a15c 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a15c 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10a15c 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f26 : InstrSpec 0x10a15e [0x41, 0x5F] (PopPre 0x10a15e) (popR64Effect 0x10a15e 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a15e 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10a15e 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f27 : InstrSpec 0x10a160 [0xC3] (RetPre 0x10a160) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10a160).toInstrSpec (ret_effect_step 0x10a160) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 86), (1, 55), (2, 79), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a153) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f21 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 86), (1, 55), (2, 79), (3, 3), (4, 88), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a157) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f22 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 91) f22 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 92) (ρ' := [(0, 86), (1, 55), (2, 79), (3, 90), (4, 91), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a158) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f23 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 94) f23 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 95) (ρ' := [(0, 86), (1, 55), (2, 79), (3, 90), (4, 94), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 93), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a15a) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f24 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 97) f24 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 98) (ρ' := [(0, 86), (1, 55), (2, 79), (3, 90), (4, 97), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 93), (13, 96), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a15c) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f25 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 100) f25 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 101) (ρ' := [(0, 86), (1, 55), (2, 79), (3, 90), (4, 100), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 93), (13, 96), (14, 99), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a15e) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f26 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 103) f26 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 104) (ρ' := [(0, 86), (1, 55), (2, 79), (3, 90), (4, 103), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 93), (13, 96), (14, 99), (15, 102), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a160) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 106) f27 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 107) (ρ' := [(0, 86), (1, 55), (2, 79), (3, 90), (4, 106), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 93), (13, 96), (14, 99), (15, 102), (22, 22), (39, 39), (50, 50), (51, 51)]) f27 (by decide) rfl rfl rfl (by decide)

theorem rest_l10a10f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a10f bytes_l10a10f) (entryMap (live .l10a10f))
      28 0x10a10f bytes_l10a10f b_l10a10f := by
  have f0 : InstrSpec 0x10a10f [0x88, 0x44, 0x24, 0x07] (StorePre 0x10a10f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10a10f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a10f 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a10f 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x10a10f 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10a113 [0x48, 0x8D, 0x4C, 0x24, 0x07] (fun s => s.RIP = 0x10a113) (leaR64Effect 0x10a113 1 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x10a113 1 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x10a113 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10a118 [0x0F, 0xB6, 0x4C, 0x24, 0x07] (LoadPre 0x10a118 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10a118 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a118 5 1 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a118 5 1 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x10a118 1 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10a11d [0x31, 0xD2] (fun s => s.RIP = 0x10a11d) (xorR32R32Effect 0x10a11d 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a11d 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x10a11d 0xd2 (by decide)) pre_rip
  have f4 : InstrSpec 0x10a11f [0x31, 0xF6] (fun s => s.RIP = 0x10a11f) (xorR32R32Effect 0x10a11f 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a11f 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x10a11f 0xf6 (by decide)) pre_rip
  have f5 : InstrSpec 0x10a121 [0x84, 0xC9] (fun s => s.RIP = 0x10a121) (testR8R8Effect 0x10a121 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10a121 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x10a121 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10a123 [0x49, 0x0F, 0x45, 0xF6] (fun s => s.RIP = 0x10a123) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a123 4 6 14))
      [.gpr 6, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 6, .rip] :=
    (cmovR64R64Effect_footprint 0x10a123 4 6 14 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10a123 5 0x49 (by decide) 0xf6 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x10a127 [0x31, 0xFF] (fun s => s.RIP = 0x10a127) (xorR32R32Effect 0x10a127 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a127 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x10a127 0xff (by decide)) pre_rip
  have f8 : InstrSpec 0x10a129 [0x84, 0xC9] (fun s => s.RIP = 0x10a129) (testR8R8Effect 0x10a129 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10a129 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x10a129 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10a12b [0x49, 0x0F, 0x45, 0xFF] (fun s => s.RIP = 0x10a12b) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a12b 4 7 15))
      [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (cmovR64R64Effect_footprint 0x10a12b 4 7 15 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10a12b 5 0x49 (by decide) 0xff (by decide) c)) pre_rip
  have f10 : InstrSpec 0x10a12f [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x10a12f) (xorR32R32Effect 0x10a12f 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a12f 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a12f 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10a132 [0x84, 0xC9] (fun s => s.RIP = 0x10a132) (testR8R8Effect 0x10a132 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10a132 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x10a132 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10a134 [0x4D, 0x0F, 0x45, 0xC4] (fun s => s.RIP = 0x10a134) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a134 4 8 12))
      [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 8, .rip] :=
    (cmovR64R64Effect_footprint 0x10a134 4 8 12 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10a134 5 0x4d (by decide) 0xc4 (by decide) c)) pre_rip
  have f13 : InstrSpec 0x10a138 [0x84, 0xC9] (fun s => s.RIP = 0x10a138) (testR8R8Effect 0x10a138 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10a138 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x10a138 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10a13a [0x49, 0x0F, 0x45, 0xD5] (fun s => s.RIP = 0x10a13a) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a13a 4 2 13))
      [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x10a13a 4 2 13 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10a13a 5 0x49 (by decide) 0xd5 (by decide) c)) pre_rip
  have f15 : InstrSpec 0x10a13e [0x48, 0x89, 0x33] (StorePre 0x10a13e 3 (fun s => AddrMode.addr (.base 3 .none) s (0x10a13e + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10a13e 6 (.base 3 .none))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a13e 6 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10a13e 0x48 (by decide) 6 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x10a141 [0x48, 0x89, 0x7B, 0x08] (StorePre 0x10a141 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10a141 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a141 7 (.base 3 (.d8 0x8)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a141 7 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10a141 0x48 (by decide) 7 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x10a145 [0x4C, 0x89, 0x43, 0x10] (StorePre 0x10a145 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10a145 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a145 8 (.base 3 (.d8 0x10)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a145 8 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10a145 0x4c (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x10a149 [0x48, 0x89, 0x53, 0x18] (StorePre 0x10a149 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x10a149 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a149 2 (.base 3 (.d8 0x18)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a149 2 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10a149 0x48 (by decide) 2 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x10a14d [0x88, 0x43, 0x20] (StorePre 0x10a14d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x10a14d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a14d 3 0 (.base 3 (.d8 0x20)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a14d 3 0 (.base 3 (.d8 0x20))).toInstrSpec (mov_m8_r8_effect_step 0x10a14d 0 (by decide) (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a113) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a118) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a11d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a11f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a121) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a123) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a127) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a129) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a12b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a12f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 71), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a132) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 71), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a134) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a138) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a13a) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 55), (2, 79), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a13e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 55), (2, 79), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a141) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 55), (2, 79), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a145) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 55), (2, 79), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a149) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 55), (2, 79), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a14d) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 55), (2, 79), (3, 3), (4, 4), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a150) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10a10f_1 code

theorem block_l10a10f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a10f :=
  Rest.liftedBlock (rest_l10a10f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a10f x hx)

theorem rest_l10a170_2 [Bindings] (code : CodeMap) :
    Rest (n := 128) code lifted (codeRange 0x10a170 bytes_l10a170) [(0, 126), (1, 109), (2, 113), (3, 3), (4, 53), (5, 5), (6, 121), (7, 7), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x10a209 bytes_l10a170_2 b_l10a170_2 := by
  have f40 : InstrSpec 0x10a209 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x10a209) (movzxR32R8Effect 0x10a209 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x10a209 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x10a209 0xf8 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x10a20c [0xE8, 0x3F, 0xDB, 0x01, 0x00] (PushPre 0x10a20c 5) (callEffect (fun _ => 0x127d50) 0x10a211)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a20c 0x127d50 0x10a211).toInstrSpec (call_rel32_effect_step 0x10a20c 0x1db3f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f40 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 126), (1, 109), (2, 113), (3, 3), (4, 53), (5, 5), (6, 121), (7, 128), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a20c) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f41 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 126), (1, 109), (2, 113), (3, 3), (4, 130), (5, 5), (6, 121), (7, 128), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f41 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 132) (by decide) (by decide) rfl rfl

theorem rest_l10a170_1 [Bindings] (code : CodeMap) :
    Rest (n := 90) code lifted (codeRange 0x10a170 bytes_l10a170) [(1, 88), (2, 71), (3, 3), (4, 53), (5, 5), (6, 83), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      22 0x10a1be bytes_l10a170_1 b_l10a170_1 := by
  have f20 : InstrSpec 0x10a1be [0x31, 0xD2] (fun s => s.RIP = 0x10a1be) (xorR32R32Effect 0x10a1be 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a1be 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x10a1be 0xd2 (by decide)) pre_rip
  have f21 : InstrSpec 0x10a1c0 [0x48, 0x8B, 0x77, 0x10] (LoadPre 0x10a1c0 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x10a1c0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a1c0 6 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10a1c0 6 (.base 7 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10a1c0 0x48 (by decide) 6 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x10a1c4 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x10a1c4) (sarR64Effect 0x10a1c4 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x10a1c4 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x10a1c4 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x10a1c8 [0x49, 0x89, 0xF0] (fun s => s.RIP = 0x10a1c8) (movR64R64Effect 0x10a1c8 8 6)
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10a1c8 8 6).toInstrSpec (mov_r64_r64_effect_step 0x10a1c8 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x10a1cb [0x49, 0xF7, 0xD0] (fun s => s.RIP = 0x10a1cb) (notR64Effect 0x10a1cb 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (notR64Effect_footprint 0x10a1cb 8).toInstrSpec (not_r64_effect_step 0x10a1cb 0x49 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x10a1ce [0x49, 0x01, 0xC8] (fun s => s.RIP = 0x10a1ce) (addR64R64Effect 0x10a1ce 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10a1ce 8 1).toInstrSpec (add_r64_r64_effect_step 0x10a1ce 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10a1d1 [0x49, 0x21, 0xF0] (fun s => s.RIP = 0x10a1d1) (andR64R64Effect 0x10a1d1 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a1d1 8 6).toInstrSpec (and_r64_r64_effect_step 0x10a1d1 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x10a1d4 [0x49, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x10a1d4) (shrR64Effect 0x10a1d4 4 8 63)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a1d4 4 8 63).toInstrSpec (shr_r64_imm8_effect_step 0x10a1d4 0x49 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10a1d8 [0x4C, 0x89, 0x04, 0x24] (StorePre 0x10a1d8 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a1d8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a1d8 8 (.sib 4 none 0 .none))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a1d8 8 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10a1d8 0x4c (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x10a1dc [0x48, 0x2B, 0x14, 0x24] (LoadPre 0x10a1dc (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a1dc + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10a1dc 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10a1dc 2 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x10a1dc 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x10a1e0 [0x48, 0x8B, 0x4F, 0x18] (LoadPre 0x10a1e0 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x10a1e0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a1e0 1 (.base 7 (.d8 0x18)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10a1e0 1 (.base 7 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10a1e0 0x48 (by decide) 1 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x10a1e4 [0x48, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x10a1e4) (sarR64Effect 0x10a1e4 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (sarR64Effect_footprint 0x10a1e4 4 2 63).toInstrSpec (sar_r64_imm8_effect_step 0x10a1e4 0x48 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10a1e8 [0x48, 0x29, 0xCA] (fun s => s.RIP = 0x10a1e8) (subR64R64Effect 0x10a1e8 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10a1e8 2 1).toInstrSpec (sub_r64_r64_effect_step 0x10a1e8 0x48 0xca (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x10a1eb [0x48, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x10a1eb) (movR64Imm64Effect 0x10a1eb 6 0x7fffffffffffffff)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x10a1eb 6 0x7fffffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x10a1eb 0x48 0xbe (by decide) (by decide) 0x7fffffffffffffff) pre_rip
  have f34 : InstrSpec 0x10a1f5 [0x48, 0x01, 0xD6] (fun s => s.RIP = 0x10a1f5) (addR64R64Effect 0x10a1f5 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10a1f5 6 2).toInstrSpec (add_r64_r64_effect_step 0x10a1f5 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x10a1f8 [0x48, 0x09, 0xCE] (fun s => s.RIP = 0x10a1f8) (orR64R64Effect 0x10a1f8 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a1f8 6 1).toInstrSpec (or_r64_r64_effect_step 0x10a1f8 0x48 0xce (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x10a1fb [0x48, 0xC1, 0xEE, 0x3F] (fun s => s.RIP = 0x10a1fb) (shrR64Effect 0x10a1fb 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a1fb 4 6 63).toInstrSpec (shr_r64_imm8_effect_step 0x10a1fb 0x48 0xee 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x10a1ff [0x48, 0x89, 0x34, 0x24] (StorePre 0x10a1ff 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a1ff + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a1ff 6 (.sib 4 none 0 .none))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a1ff 6 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10a1ff 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x10a203 [0x0F, 0xB6, 0x04, 0x24] (LoadPre 0x10a203 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a203 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a203 4 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a203 4 0 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x10a203 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x10a207 [0x24, 0x01] (fun s => s.RIP = 0x10a207) (andAlImm8Effect 0x10a207 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x10a207 0x1).toInstrSpec (and_al_imm8_effect_step 0x10a207 0x1) pre_rip
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(1, 88), (2, 90), (3, 3), (4, 53), (5, 5), (6, 83), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1c0) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(1, 88), (2, 90), (3, 3), (4, 53), (5, 5), (6, 92), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1c4) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(1, 94), (2, 90), (3, 3), (4, 53), (5, 5), (6, 92), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1c8) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f23 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(1, 94), (2, 90), (3, 3), (4, 53), (5, 5), (6, 92), (7, 7), (8, 96), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1cb) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f24 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(1, 94), (2, 90), (3, 3), (4, 53), (5, 5), (6, 92), (7, 7), (8, 98), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1ce) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f25 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(1, 94), (2, 90), (3, 3), (4, 53), (5, 5), (6, 92), (7, 7), (8, 100), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1d1) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f26 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(1, 94), (2, 90), (3, 3), (4, 53), (5, 5), (6, 92), (7, 7), (8, 102), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1d4) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f27 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(1, 94), (2, 90), (3, 3), (4, 53), (5, 5), (6, 92), (7, 7), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1d8) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(1, 94), (2, 90), (3, 3), (4, 53), (5, 5), (6, 92), (7, 7), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1dc) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f29 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(1, 94), (2, 107), (3, 3), (4, 53), (5, 5), (6, 92), (7, 7), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1e0) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f30 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(1, 109), (2, 107), (3, 3), (4, 53), (5, 5), (6, 92), (7, 7), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1e4) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f31 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(1, 109), (2, 111), (3, 3), (4, 53), (5, 5), (6, 92), (7, 7), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1e8) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f32 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(1, 109), (2, 113), (3, 3), (4, 53), (5, 5), (6, 92), (7, 7), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1eb) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f33 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(1, 109), (2, 113), (3, 3), (4, 53), (5, 5), (6, 115), (7, 7), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1f5) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f34 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(1, 109), (2, 113), (3, 3), (4, 53), (5, 5), (6, 117), (7, 7), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1f8) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f35 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(1, 109), (2, 113), (3, 3), (4, 53), (5, 5), (6, 119), (7, 7), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1fb) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(1, 109), (2, 113), (3, 3), (4, 53), (5, 5), (6, 121), (7, 7), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1ff) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.exec (n := 123) (ρ' := [(1, 109), (2, 113), (3, 3), (4, 53), (5, 5), (6, 121), (7, 7), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a203) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f38 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 124), (1, 109), (2, 113), (3, 3), (4, 53), (5, 5), (6, 121), (7, 7), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a207) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f39 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 126), (1, 109), (2, 113), (3, 3), (4, 53), (5, 5), (6, 121), (7, 7), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a209) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a170_2 code

theorem rest_l10a170 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a170 bytes_l10a170) (entryMap (live .l10a170))
      42 0x10a170 bytes_l10a170 b_l10a170 := by
  have f0 : InstrSpec 0x10a170 [0x50] (PushPre 0x10a170 1) (pushR64Effect 0x10a170 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a170 1 0).toInstrSpec (push_r64_effect_step 0x10a170 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10a171 [0x48, 0x8B, 0x07] (LoadPre 0x10a171 (fun s => AddrMode.addr (.base 7 .none) s (0x10a171 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a171 0 (.base 7 .none))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10a171 0 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10a171 0x48 (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10a174 [0x48, 0xB9, 0xA0, 0x20, 0x1B, 0x68, 0x46, 0x2F, 0xE9, 0xDF] (fun s => s.RIP = 0x10a174) (movR64Imm64Effect 0x10a174 1 0xdfe92f46681b20a0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10a174 1 0xdfe92f46681b20a0).toInstrSpec (mov_r64_imm64_effect_step 0x10a174 0x48 0xb9 (by decide) (by decide) 0xdfe92f46681b20a0) pre_rip
  have f3 : InstrSpec 0x10a17e [0x48, 0x29, 0xC1] (fun s => s.RIP = 0x10a17e) (subR64R64Effect 0x10a17e 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10a17e 1 0).toInstrSpec (sub_r64_r64_effect_step 0x10a17e 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10a181 [0x48, 0x21, 0xC1] (fun s => s.RIP = 0x10a181) (andR64R64Effect 0x10a181 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a181 1 0).toInstrSpec (and_r64_r64_effect_step 0x10a181 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10a184 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x10a184) (shrR64Effect 0x10a184 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a184 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x10a184 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10a188 [0x48, 0x89, 0x0C, 0x24] (StorePre 0x10a188 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a188 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a188 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a188 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10a188 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10a18c [0x48, 0x89, 0xE0] (fun s => s.RIP = 0x10a18c) (movR64R64Effect 0x10a18c 0 4)
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10a18c 0 4).toInstrSpec (mov_r64_r64_effect_step 0x10a18c 0x48 0xe0 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10a18f [0x31, 0xC9] (fun s => s.RIP = 0x10a18f) (xorR32R32Effect 0x10a18f 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a18f 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x10a18f 0xc9 (by decide)) pre_rip
  have f9 : InstrSpec 0x10a191 [0x48, 0x2B, 0x0C, 0x24] (LoadPre 0x10a191 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a191 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10a191 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10a191 1 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x10a191 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x10a195 [0x48, 0x8B, 0x57, 0x08] (LoadPre 0x10a195 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10a195 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a195 2 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10a195 2 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10a195 0x48 (by decide) 2 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10a199 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x10a199) (sarR64Effect 0x10a199 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x10a199 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x10a199 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10a19d [0x48, 0x29, 0xD1] (fun s => s.RIP = 0x10a19d) (subR64R64Effect 0x10a19d 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10a19d 1 2).toInstrSpec (sub_r64_r64_effect_step 0x10a19d 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10a1a0 [0x48, 0xBE, 0x1D, 0x50, 0xA4, 0x57, 0x73, 0x6E, 0x57, 0x5D] (fun s => s.RIP = 0x10a1a0) (movR64Imm64Effect 0x10a1a0 6 0x5d576e7357a4501d)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x10a1a0 6 0x5d576e7357a4501d).toInstrSpec (mov_r64_imm64_effect_step 0x10a1a0 0x48 0xbe (by decide) (by decide) 0x5d576e7357a4501d) pre_rip
  have f14 : InstrSpec 0x10a1aa [0x48, 0x01, 0xCE] (fun s => s.RIP = 0x10a1aa) (addR64R64Effect 0x10a1aa 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10a1aa 6 1).toInstrSpec (add_r64_r64_effect_step 0x10a1aa 0x48 0xce (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10a1ad [0x48, 0x09, 0xD6] (fun s => s.RIP = 0x10a1ad) (orR64R64Effect 0x10a1ad 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a1ad 6 2).toInstrSpec (or_r64_r64_effect_step 0x10a1ad 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10a1b0 [0x48, 0xC1, 0xEE, 0x3F] (fun s => s.RIP = 0x10a1b0) (shrR64Effect 0x10a1b0 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a1b0 4 6 63).toInstrSpec (shr_r64_imm8_effect_step 0x10a1b0 0x48 0xee 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10a1b4 [0x48, 0x89, 0x34, 0x24] (StorePre 0x10a1b4 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a1b4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a1b4 6 (.sib 4 none 0 .none))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a1b4 6 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10a1b4 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x10a1b8 [0x31, 0xC9] (fun s => s.RIP = 0x10a1b8) (xorR32R32Effect 0x10a1b8 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a1b8 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x10a1b8 0xc9 (by decide)) pre_rip
  have f19 : InstrSpec 0x10a1ba [0x48, 0x2B, 0x0C, 0x24] (LoadPre 0x10a1ba (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a1ba + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10a1ba 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10a1ba 1 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x10a1ba 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 53), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a171) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a174) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 53), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a17e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 59), (3, 3), (4, 53), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a181) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 61), (3, 3), (4, 53), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a184) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 63), (3, 3), (4, 53), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a188) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 55), (1, 63), (3, 3), (4, 53), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a18c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(1, 63), (3, 3), (4, 53), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a18f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 67), (3, 3), (4, 53), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a191) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 69), (3, 3), (4, 53), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a195) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 69), (2, 71), (3, 3), (4, 53), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a199) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 73), (2, 71), (3, 3), (4, 53), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a19d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 75), (2, 71), (3, 3), (4, 53), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1a0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 75), (2, 71), (3, 3), (4, 53), (5, 5), (6, 77), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1aa) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 75), (2, 71), (3, 3), (4, 53), (5, 5), (6, 79), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1ad) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(1, 75), (2, 71), (3, 3), (4, 53), (5, 5), (6, 81), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1b0) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(1, 75), (2, 71), (3, 3), (4, 53), (5, 5), (6, 83), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1b4) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(1, 75), (2, 71), (3, 3), (4, 53), (5, 5), (6, 83), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1b8) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(1, 86), (2, 71), (3, 3), (4, 53), (5, 5), (6, 83), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1ba) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(1, 88), (2, 71), (3, 3), (4, 53), (5, 5), (6, 83), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1be) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a170_1 code

theorem block_l10a170 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a170 :=
  Rest.liftedBlock (rest_l10a170 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a170 x hx)

theorem rest_l10a211 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a211 bytes_l10a211) (entryMap (live .l10a211))
      2 0x10a211 bytes_l10a211 b_l10a211 := by
  have f0 : InstrSpec 0x10a211 [0x59] (PopPre 0x10a211) (popR64Effect 0x10a211 1 1)
      [.gpr 4] [] [.reg 1, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a211 1 1).toInstrSpec (pop_r64_effect_step 0x10a211 0x59 (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10a212 [0xC3] (RetPre 0x10a212) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10a212).toInstrSpec (ret_effect_step 0x10a212) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a212) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 57) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 58) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f1 (by decide) rfl rfl rfl (by decide)

theorem block_l10a211 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a211 :=
  Rest.liftedBlock (rest_l10a211 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a211 x hx)

theorem rest_l10a220_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x10a220 bytes_l10a220) [(0, 55), (1, 67), (2, 87), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 89), (22, 22), (39, 39), (50, 50), (51, 51)]
      7 0x10a263 bytes_l10a220_1 b_l10a220_1 := by
  have f20 : InstrSpec 0x10a263 [0x48, 0x0F, 0x45, 0xF2] (fun s => s.RIP = 0x10a263) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a263 4 6 2))
      [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 6, .rip] :=
    (cmovR64R64Effect_footprint 0x10a263 4 6 2 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10a263 5 0x48 (by decide) 0xf2 (by decide) c)) pre_rip
  have f21 : InstrSpec 0x10a267 [0x48, 0x89, 0x38] (StorePre 0x10a267 3 (fun s => AddrMode.addr (.base 0 .none) s (0x10a267 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10a267 7 (.base 0 .none))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a267 7 (.base 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10a267 0x48 (by decide) 7 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x10a26a [0x4C, 0x89, 0x40, 0x08] (StorePre 0x10a26a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x10a26a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a26a 8 (.base 0 (.d8 0x8)))
      [.gpr 8, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a26a 8 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10a26a 0x4c (by decide) 0 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x10a26e [0x4C, 0x89, 0x48, 0x10] (StorePre 0x10a26e 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x10a26e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a26e 9 (.base 0 (.d8 0x10)))
      [.gpr 9, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a26e 9 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10a26e 0x4c (by decide) 1 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x10a272 [0x48, 0x89, 0x70, 0x18] (StorePre 0x10a272 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x10a272 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a272 6 (.base 0 (.d8 0x18)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a272 6 (.base 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10a272 0x48 (by decide) 6 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x10a276 [0x48, 0x83, 0xC4, 0x01] (fun s => s.RIP = 0x10a276) (addR64Imm8Effect 0x10a276 4 0x1)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10a276 4 0x1).toInstrSpec (add_r64_imm8_effect_step 0x10a276 0x48 0xc4 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10a27a [0xC3] (RetPre 0x10a27a) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10a27a).toInstrSpec (ret_effect_step 0x10a27a) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 53), (5, 5), (6, 91), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a267) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 53), (5, 5), (6, 91), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a26a) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 53), (5, 5), (6, 91), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a26e) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 53), (5, 5), (6, 91), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a272) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 53), (5, 5), (6, 91), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a276) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f25 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 97), (5, 5), (6, 91), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a27a) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f26 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 100) f26 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 101) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 100), (5, 5), (6, 91), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f26 (by decide) rfl rfl rfl (by decide)

theorem rest_l10a220 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a220 bytes_l10a220) (entryMap (live .l10a220))
      27 0x10a220 bytes_l10a220 b_l10a220 := by
  have f0 : InstrSpec 0x10a220 [0x48, 0x83, 0xEC, 0x01] (fun s => s.RIP = 0x10a220) (subR64Imm8Effect 0x10a220 4 0x1)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10a220 4 0x1).toInstrSpec (sub_r64_imm8_effect_step 0x10a220 0x48 0xec 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10a224 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x10a224) (movR64R64Effect 0x10a224 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10a224 0 7).toInstrSpec (mov_r64_r64_effect_step 0x10a224 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10a227 [0x48, 0x8B, 0x3E] (LoadPre 0x10a227 (fun s => AddrMode.addr (.base 6 .none) s (0x10a227 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a227 7 (.base 6 .none))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10a227 7 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10a227 0x48 (by decide) 7 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10a22a [0x4C, 0x8B, 0x46, 0x08] (LoadPre 0x10a22a (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10a22a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a22a 8 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10a22a 8 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10a22a 0x4c (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10a22e [0x4C, 0x8B, 0x4E, 0x10] (LoadPre 0x10a22e (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10a22e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a22e 9 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x10a22e 9 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10a22e 0x4c (by decide) 1 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10a232 [0x48, 0x8B, 0x76, 0x18] (LoadPre 0x10a232 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10a232 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a232 6 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10a232 6 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10a232 0x48 (by decide) 6 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10a236 [0x88, 0x0C, 0x24] (StorePre 0x10a236 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a236 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a236 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a236 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x10a236 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10a239 [0x48, 0x89, 0xE1] (fun s => s.RIP = 0x10a239) (movR64R64Effect 0x10a239 1 4)
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10a239 1 4).toInstrSpec (mov_r64_r64_effect_step 0x10a239 0x48 0xe1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10a23c [0x0F, 0xB6, 0x0C, 0x24] (LoadPre 0x10a23c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a23c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a23c 4 1 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a23c 4 1 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x10a23c 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10a240 [0x4C, 0x8B, 0x12] (LoadPre 0x10a240 (fun s => AddrMode.addr (.base 2 .none) s (0x10a240 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a240 10 (.base 2 .none))
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x10a240 10 (.base 2 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10a240 0x4c (by decide) 2 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x10a243 [0x4C, 0x8B, 0x5A, 0x08] (LoadPre 0x10a243 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x10a243 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a243 11 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x10a243 11 (.base 2 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10a243 0x4c (by decide) 3 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10a247 [0x84, 0xC9] (fun s => s.RIP = 0x10a247) (testR8R8Effect 0x10a247 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10a247 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x10a247 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10a249 [0x49, 0x0F, 0x45, 0xFA] (fun s => s.RIP = 0x10a249) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a249 4 7 10))
      [.gpr 7, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (cmovR64R64Effect_footprint 0x10a249 4 7 10 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10a249 5 0x49 (by decide) 0xfa (by decide) c)) pre_rip
  have f13 : InstrSpec 0x10a24d [0x84, 0xC9] (fun s => s.RIP = 0x10a24d) (testR8R8Effect 0x10a24d 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10a24d 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x10a24d 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10a24f [0x4D, 0x0F, 0x45, 0xC3] (fun s => s.RIP = 0x10a24f) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a24f 4 8 11))
      [.gpr 8, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 8, .rip] :=
    (cmovR64R64Effect_footprint 0x10a24f 4 8 11 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10a24f 5 0x4d (by decide) 0xc3 (by decide) c)) pre_rip
  have f15 : InstrSpec 0x10a253 [0x4C, 0x8B, 0x52, 0x10] (LoadPre 0x10a253 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x10a253 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a253 10 (.base 2 (.d8 0x10)))
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x10a253 10 (.base 2 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10a253 0x4c (by decide) 2 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10a257 [0x84, 0xC9] (fun s => s.RIP = 0x10a257) (testR8R8Effect 0x10a257 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10a257 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x10a257 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10a259 [0x4D, 0x0F, 0x45, 0xCA] (fun s => s.RIP = 0x10a259) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a259 4 9 10))
      [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 9, .rip] :=
    (cmovR64R64Effect_footprint 0x10a259 4 9 10 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10a259 5 0x4d (by decide) 0xca (by decide) c)) pre_rip
  have f18 : InstrSpec 0x10a25d [0x48, 0x8B, 0x52, 0x18] (LoadPre 0x10a25d (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x10a25d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a25d 2 (.base 2 (.d8 0x18)))
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10a25d 2 (.base 2 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10a25d 0x48 (by decide) 2 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x10a261 [0x84, 0xC9] (fun s => s.RIP = 0x10a261) (testR8R8Effect 0x10a261 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10a261 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x10a261 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a224) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a227) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a22a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 57), (8, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a22e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 57), (8, 59), (9, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a232) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 57), (8, 59), (9, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a236) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 57), (8, 59), (9, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a239) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 57), (8, 59), (9, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a23c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 57), (8, 59), (9, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a240) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 57), (8, 59), (9, 61), (10, 69), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a243) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 57), (8, 59), (9, 61), (10, 69), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a247) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 57), (8, 59), (9, 61), (10, 69), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a249) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 59), (9, 61), (10, 69), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a24d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 59), (9, 61), (10, 69), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a24f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 79), (9, 61), (10, 69), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a253) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 79), (9, 61), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a257) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 79), (9, 61), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a259) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a25d) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a261) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a263) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a220_1 code

theorem block_l10a220 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a220 :=
  Rest.liftedBlock (rest_l10a220 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a220 x hx)

theorem rest_l10a280 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a280 bytes_l10a280) (entryMap (live .l10a280))
      5 0x10a280 bytes_l10a280 b_l10a280 := by
  have f0 : InstrSpec 0x10a280 [0x50] (PushPre 0x10a280 1) (pushR64Effect 0x10a280 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a280 1 0).toInstrSpec (push_r64_effect_step 0x10a280 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10a281 [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x10a281) (movR64R64Effect 0x10a281 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a281 2 6).toInstrSpec (mov_r64_r64_effect_step 0x10a281 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10a284 [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a284) (movR32Imm32Effect 0x10a284 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10a284 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x10a284 0xbe (by decide) 0x4) pre_rip
  have f3 : InstrSpec 0x10a289 [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a289) (movR32Imm32Effect 0x10a289 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10a289 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x10a289 0xb9 (by decide) 0x4) pre_rip
  have f4 : InstrSpec 0x10a28e [0xE8, 0xBD, 0xDC, 0x01, 0x00] (PushPre 0x10a28e 5) (callEffect (fun _ => 0x127f50) 0x10a293)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a28e 0x127f50 0x10a293).toInstrSpec (call_rel32_effect_step 0x10a28e 0x1dcbd (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a281) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 55), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a284) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 55), (3, 3), (4, 53), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a289) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 55), (3, 3), (4, 53), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a28e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 59), (2, 55), (3, 3), (4, 61), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f50) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10a280 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a280 :=
  Rest.liftedBlock (rest_l10a280 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a280 x hx)

theorem rest_l10a293 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a293 bytes_l10a293) (entryMap (live .l10a293))
      4 0x10a293 bytes_l10a293 b_l10a293 := by
  have f0 : InstrSpec 0x10a293 [0x24, 0x01] (fun s => s.RIP = 0x10a293) (andAlImm8Effect 0x10a293 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x10a293 0x1).toInstrSpec (and_al_imm8_effect_step 0x10a293 0x1) pre_rip
  have f1 : InstrSpec 0x10a295 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x10a295) (movzxR32R8Effect 0x10a295 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x10a295 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x10a295 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10a298 [0x58] (PopPre 0x10a298) (popR64Effect 0x10a298 1 0)
      [.gpr 4] [] [.reg 0, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a298 1 0).toInstrSpec (pop_r64_effect_step 0x10a298 0x58 (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a295) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a298) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a299) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x10a299 0x1dab2 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10a293 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a293 :=
  Rest.liftedBlock (rest_l10a293 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a293 x hx)

theorem rest_l10a2a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a2a0 bytes_l10a2a0) (entryMap (live .l10a2a0))
      5 0x10a2a0 bytes_l10a2a0 b_l10a2a0 := by
  have f0 : InstrSpec 0x10a2a0 [0x50] (PushPre 0x10a2a0 1) (pushR64Effect 0x10a2a0 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a2a0 1 0).toInstrSpec (push_r64_effect_step 0x10a2a0 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10a2a1 [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x10a2a1) (movR64R64Effect 0x10a2a1 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a2a1 2 6).toInstrSpec (mov_r64_r64_effect_step 0x10a2a1 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10a2a4 [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a2a4) (movR32Imm32Effect 0x10a2a4 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10a2a4 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x10a2a4 0xbe (by decide) 0x4) pre_rip
  have f3 : InstrSpec 0x10a2a9 [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a2a9) (movR32Imm32Effect 0x10a2a9 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10a2a9 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x10a2a9 0xb9 (by decide) 0x4) pre_rip
  have f4 : InstrSpec 0x10a2ae [0xE8, 0x9D, 0xDC, 0x01, 0x00] (PushPre 0x10a2ae 5) (callEffect (fun _ => 0x127f50) 0x10a2b3)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a2ae 0x127f50 0x10a2b3).toInstrSpec (call_rel32_effect_step 0x10a2ae 0x1dc9d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2a1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 55), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2a4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 55), (3, 3), (4, 53), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2a9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 55), (3, 3), (4, 53), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2ae) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 59), (2, 55), (3, 3), (4, 61), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f50) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10a2a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a2a0 :=
  Rest.liftedBlock (rest_l10a2a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a2a0 x hx)

theorem rest_l10a2b3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a2b3 bytes_l10a2b3) (entryMap (live .l10a2b3))
      3 0x10a2b3 bytes_l10a2b3 b_l10a2b3 := by
  have f0 : InstrSpec 0x10a2b3 [0x24, 0x01] (fun s => s.RIP = 0x10a2b3) (andAlImm8Effect 0x10a2b3 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x10a2b3 0x1).toInstrSpec (and_al_imm8_effect_step 0x10a2b3 0x1) pre_rip
  have f1 : InstrSpec 0x10a2b5 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x10a2b5) (movzxR32R8Effect 0x10a2b5 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x10a2b5 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x10a2b5 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10a2b8 [0xE8, 0x93, 0xDA, 0x01, 0x00] (PushPre 0x10a2b8 5) (callEffect (fun _ => 0x127d50) 0x10a2bd)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a2b8 0x127d50 0x10a2bd).toInstrSpec (call_rel32_effect_step 0x10a2b8 0x1da93 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2b5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2b8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l10a2b3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a2b3 :=
  Rest.liftedBlock (rest_l10a2b3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a2b3 x hx)

theorem rest_l10a2bd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a2bd bytes_l10a2bd) (entryMap (live .l10a2bd))
      4 0x10a2bd bytes_l10a2bd b_l10a2bd := by
  have f0 : InstrSpec 0x10a2bd [0x84, 0xC0] (fun s => s.RIP = 0x10a2bd) (testR8R8Effect 0x10a2bd 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10a2bd 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x10a2bd 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10a2bf [0x0F, 0x95, 0xC0] (fun s => s.RIP = 0x10a2bf) (atFlags (condHolds 5) (setccR8Effect 0x10a2bf 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x10a2bf 3 0 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x10a2bf 5 0xc0 (by decide) (by decide) c)) pre_rip
  have f2 : InstrSpec 0x10a2c2 [0x59] (PopPre 0x10a2c2) (popR64Effect 0x10a2c2 1 1)
      [.gpr 4] [] [.reg 1, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a2c2 1 1).toInstrSpec (pop_r64_effect_step 0x10a2c2 0x59 (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10a2c3 [0xC3] (RetPre 0x10a2c3) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10a2c3).toInstrSpec (ret_effect_step 0x10a2c3) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2bf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2c2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 57), (2, 2), (3, 3), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2c3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 62) (ρ' := [(0, 55), (1, 57), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) f3 (by decide) rfl rfl rfl (by decide)

theorem block_l10a2bd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a2bd :=
  Rest.liftedBlock (rest_l10a2bd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a2bd x hx)

theorem rest_l10a2d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a2d0 bytes_l10a2d0) (entryMap (live .l10a2d0))
      2 0x10a2d0 bytes_l10a2d0 b_l10a2d0 := by
  have f0 : InstrSpec 0x10a2d0 [0x48, 0xC7, 0xC2, 0xA0, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x10a2d0) (movR64Imm32Effect 0x10a2d0 2 0x2021a0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10a2d0 2 0x2021a0).toInstrSpec (mov_r64_imm32_effect_step 0x10a2d0 0x48 0xc2 (by decide) (by decide) (by decide) 0x2021a0) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2d7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x10a2d7 0x68a4 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10a2d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a2d0 :=
  Rest.liftedBlock (rest_l10a2d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a2d0 x hx)

theorem rest_l10a2e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a2e0 bytes_l10a2e0) (entryMap (live .l10a2e0))
      2 0x10a2e0 bytes_l10a2e0 b_l10a2e0 := by
  have f0 : InstrSpec 0x10a2e0 [0x48, 0xC7, 0xC1, 0xA0, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x10a2e0) (movR64Imm32Effect 0x10a2e0 1 0x2021a0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x10a2e0 1 0x2021a0).toInstrSpec (mov_r64_imm32_effect_step 0x10a2e0 0x48 0xc1 (by decide) (by decide) (by decide) 0x2021a0) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2e7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x10a2e7 0x66c4 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10a2e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a2e0 :=
  Rest.liftedBlock (rest_l10a2e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a2e0 x hx)

theorem rest_l10a2f0_4 [Bindings] (code : CodeMap) :
    Rest (n := 186) code lifted (codeRange 0x10a2f0 bytes_l10a2f0) [(0, 53), (1, 165), (2, 184), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      10 0x10a3ec bytes_l10a2f0_4 b_l10a2f0_4 := by
  have f80 : InstrSpec 0x10a3ec [0x88, 0x57, 0x1B] (StorePre 0x10a3ec 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1b)) s (0x10a3ec + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3ec 3 2 (.base 7 (.d8 0x1b)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a3ec 3 2 (.base 7 (.d8 0x1b))).toInstrSpec (mov_m8_r8_effect_step 0x10a3ec 2 (by decide) (.base 7 (.d8 0x1b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f81 : InstrSpec 0x10a3ef [0x89, 0xCA] (fun s => s.RIP = 0x10a3ef) (movR32R32Effect 0x10a3ef 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x10a3ef 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x10a3ef 0xca (by decide)) pre_rip
  have f82 : InstrSpec 0x10a3f1 [0xC1, 0xEA, 0x18] (fun s => s.RIP = 0x10a3f1) (shrR32Effect 0x10a3f1 3 2 24)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a3f1 3 2 24).toInstrSpec (shr_r32_imm8_effect_step 0x10a3f1 0xea 0x18 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x10a3f4 [0x88, 0x57, 0x1C] (StorePre 0x10a3f4 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1c)) s (0x10a3f4 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3f4 3 2 (.base 7 (.d8 0x1c)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a3f4 3 2 (.base 7 (.d8 0x1c))).toInstrSpec (mov_m8_r8_effect_step 0x10a3f4 2 (by decide) (.base 7 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f84 : InstrSpec 0x10a3f7 [0x89, 0xCA] (fun s => s.RIP = 0x10a3f7) (movR32R32Effect 0x10a3f7 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x10a3f7 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x10a3f7 0xca (by decide)) pre_rip
  have f85 : InstrSpec 0x10a3f9 [0xC1, 0xEA, 0x10] (fun s => s.RIP = 0x10a3f9) (shrR32Effect 0x10a3f9 3 2 16)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a3f9 3 2 16).toInstrSpec (shr_r32_imm8_effect_step 0x10a3f9 0xea 0x10 (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x10a3fc [0x88, 0x57, 0x1D] (StorePre 0x10a3fc 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1d)) s (0x10a3fc + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3fc 3 2 (.base 7 (.d8 0x1d)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a3fc 3 2 (.base 7 (.d8 0x1d))).toInstrSpec (mov_m8_r8_effect_step 0x10a3fc 2 (by decide) (.base 7 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f87 : InstrSpec 0x10a3ff [0x88, 0x6F, 0x1E] (StorePre 0x10a3ff 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1e)) s (0x10a3ff + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a3ff 3 5 (.base 7 (.d8 0x1e)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x10a3ff 3 5 (.base 7 (.d8 0x1e))).toInstrSpec (mov_m8_r8_norex_effect_step 0x10a3ff 5 (.base 7 (.d8 0x1e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f88 : InstrSpec 0x10a402 [0x88, 0x4F, 0x1F] (StorePre 0x10a402 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1f)) s (0x10a402 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a402 3 1 (.base 7 (.d8 0x1f)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a402 3 1 (.base 7 (.d8 0x1f))).toInstrSpec (mov_m8_r8_effect_step 0x10a402 1 (by decide) (.base 7 (.d8 0x1f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f89 : InstrSpec 0x10a405 [0xC3] (RetPre 0x10a405) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10a405).toInstrSpec (ret_effect_step 0x10a405) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 186) (RestInside.exec (n := 186) (ρ' := [(0, 53), (1, 165), (2, 184), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3ef) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f81 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 53), (1, 165), (2, 187), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3f1) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f82 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 53), (1, 165), (2, 189), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3f4) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.exec (n := 191) (ρ' := [(0, 53), (1, 165), (2, 189), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3f7) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 192) (RestInside.out (n := 192) f84 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 193) (ρ' := [(0, 53), (1, 165), (2, 192), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3f9) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 194) (RestInside.out (n := 194) f85 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 195) (ρ' := [(0, 53), (1, 165), (2, 194), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3fc) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 196) (RestInside.exec (n := 196) (ρ' := [(0, 53), (1, 165), (2, 194), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3ff) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 197) (RestInside.exec (n := 197) (ρ' := [(0, 53), (1, 165), (2, 194), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a402) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 198) (RestInside.exec (n := 198) (ρ' := [(0, 53), (1, 165), (2, 194), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a405) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f89 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 200) f89 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 201) (ρ' := [(0, 53), (1, 165), (2, 194), (3, 3), (4, 200), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f89 (by decide) rfl rfl rfl (by decide)

theorem rest_l10a2f0_3 [Bindings] (code : CodeMap) :
    Rest (n := 153) code lifted (codeRange 0x10a2f0 bytes_l10a2f0) [(0, 53), (1, 129), (2, 151), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      30 0x10a3ac bytes_l10a2f0_3 b_l10a2f0_3 := by
  have f60 : InstrSpec 0x10a3ac [0xC1, 0xEA, 0x18] (fun s => s.RIP = 0x10a3ac) (shrR32Effect 0x10a3ac 3 2 24)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a3ac 3 2 24).toInstrSpec (shr_r32_imm8_effect_step 0x10a3ac 0xea 0x18 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x10a3af [0x88, 0x57, 0x14] (StorePre 0x10a3af 3 (fun s => AddrMode.addr (.base 7 (.d8 0x14)) s (0x10a3af + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3af 3 2 (.base 7 (.d8 0x14)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a3af 3 2 (.base 7 (.d8 0x14))).toInstrSpec (mov_m8_r8_effect_step 0x10a3af 2 (by decide) (.base 7 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f62 : InstrSpec 0x10a3b2 [0x89, 0xCA] (fun s => s.RIP = 0x10a3b2) (movR32R32Effect 0x10a3b2 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x10a3b2 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x10a3b2 0xca (by decide)) pre_rip
  have f63 : InstrSpec 0x10a3b4 [0xC1, 0xEA, 0x10] (fun s => s.RIP = 0x10a3b4) (shrR32Effect 0x10a3b4 3 2 16)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a3b4 3 2 16).toInstrSpec (shr_r32_imm8_effect_step 0x10a3b4 0xea 0x10 (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x10a3b7 [0x88, 0x57, 0x15] (StorePre 0x10a3b7 3 (fun s => AddrMode.addr (.base 7 (.d8 0x15)) s (0x10a3b7 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3b7 3 2 (.base 7 (.d8 0x15)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a3b7 3 2 (.base 7 (.d8 0x15))).toInstrSpec (mov_m8_r8_effect_step 0x10a3b7 2 (by decide) (.base 7 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f65 : InstrSpec 0x10a3ba [0x88, 0x6F, 0x16] (StorePre 0x10a3ba 3 (fun s => AddrMode.addr (.base 7 (.d8 0x16)) s (0x10a3ba + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a3ba 3 5 (.base 7 (.d8 0x16)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x10a3ba 3 5 (.base 7 (.d8 0x16))).toInstrSpec (mov_m8_r8_norex_effect_step 0x10a3ba 5 (.base 7 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f66 : InstrSpec 0x10a3bd [0x88, 0x4F, 0x17] (StorePre 0x10a3bd 3 (fun s => AddrMode.addr (.base 7 (.d8 0x17)) s (0x10a3bd + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3bd 3 1 (.base 7 (.d8 0x17)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a3bd 3 1 (.base 7 (.d8 0x17))).toInstrSpec (mov_m8_r8_effect_step 0x10a3bd 1 (by decide) (.base 7 (.d8 0x17)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f67 : InstrSpec 0x10a3c0 [0x48, 0x8B, 0x4E, 0x18] (LoadPre 0x10a3c0 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10a3c0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a3c0 1 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10a3c0 1 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10a3c0 0x48 (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f68 : InstrSpec 0x10a3c4 [0x48, 0x0F, 0xC9] (fun s => s.RIP = 0x10a3c4) (bswapR64Effect 0x10a3c4 3 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR64Effect_footprint 0x10a3c4 3 1).toInstrSpec (bswap_r64_effect_step 0x10a3c4 0x48 (by decide) 0xc9 (by decide)) pre_rip
  have f69 : InstrSpec 0x10a3c7 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x10a3c7) (movR64R64Effect 0x10a3c7 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a3c7 2 1).toInstrSpec (mov_r64_r64_effect_step 0x10a3c7 0x48 0xca (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x10a3ca [0x48, 0xC1, 0xEA, 0x38] (fun s => s.RIP = 0x10a3ca) (shrR64Effect 0x10a3ca 4 2 56)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a3ca 4 2 56).toInstrSpec (shr_r64_imm8_effect_step 0x10a3ca 0x48 0xea 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x10a3ce [0x88, 0x57, 0x18] (StorePre 0x10a3ce 3 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x10a3ce + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3ce 3 2 (.base 7 (.d8 0x18)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a3ce 3 2 (.base 7 (.d8 0x18))).toInstrSpec (mov_m8_r8_effect_step 0x10a3ce 2 (by decide) (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f72 : InstrSpec 0x10a3d1 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x10a3d1) (movR64R64Effect 0x10a3d1 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a3d1 2 1).toInstrSpec (mov_r64_r64_effect_step 0x10a3d1 0x48 0xca (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x10a3d4 [0x48, 0xC1, 0xEA, 0x30] (fun s => s.RIP = 0x10a3d4) (shrR64Effect 0x10a3d4 4 2 48)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a3d4 4 2 48).toInstrSpec (shr_r64_imm8_effect_step 0x10a3d4 0x48 0xea 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x10a3d8 [0x88, 0x57, 0x19] (StorePre 0x10a3d8 3 (fun s => AddrMode.addr (.base 7 (.d8 0x19)) s (0x10a3d8 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3d8 3 2 (.base 7 (.d8 0x19)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a3d8 3 2 (.base 7 (.d8 0x19))).toInstrSpec (mov_m8_r8_effect_step 0x10a3d8 2 (by decide) (.base 7 (.d8 0x19)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f75 : InstrSpec 0x10a3db [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x10a3db) (movR64R64Effect 0x10a3db 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a3db 2 1).toInstrSpec (mov_r64_r64_effect_step 0x10a3db 0x48 0xca (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x10a3de [0x48, 0xC1, 0xEA, 0x28] (fun s => s.RIP = 0x10a3de) (shrR64Effect 0x10a3de 4 2 40)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a3de 4 2 40).toInstrSpec (shr_r64_imm8_effect_step 0x10a3de 0x48 0xea 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x10a3e2 [0x88, 0x57, 0x1A] (StorePre 0x10a3e2 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1a)) s (0x10a3e2 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3e2 3 2 (.base 7 (.d8 0x1a)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a3e2 3 2 (.base 7 (.d8 0x1a))).toInstrSpec (mov_m8_r8_effect_step 0x10a3e2 2 (by decide) (.base 7 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f78 : InstrSpec 0x10a3e5 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x10a3e5) (movR64R64Effect 0x10a3e5 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a3e5 2 1).toInstrSpec (mov_r64_r64_effect_step 0x10a3e5 0x48 0xca (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x10a3e8 [0x48, 0xC1, 0xEA, 0x20] (fun s => s.RIP = 0x10a3e8) (shrR64Effect 0x10a3e8 4 2 32)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a3e8 4 2 32).toInstrSpec (shr_r64_imm8_effect_step 0x10a3e8 0x48 0xea 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f60 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 53), (1, 129), (2, 153), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3af) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.exec (n := 155) (ρ' := [(0, 53), (1, 129), (2, 153), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3b2) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f62 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 53), (1, 129), (2, 156), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3b4) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f63 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 53), (1, 129), (2, 158), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3b7) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.exec (n := 160) (ρ' := [(0, 53), (1, 129), (2, 158), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3ba) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 161) (RestInside.exec (n := 161) (ρ' := [(0, 53), (1, 129), (2, 158), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3bd) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 162) (RestInside.exec (n := 162) (ρ' := [(0, 53), (1, 129), (2, 158), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3c0) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f67 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 53), (1, 163), (2, 158), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3c4) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f68 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 53), (1, 165), (2, 158), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3c7) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f69 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 53), (1, 165), (2, 167), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3ca) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f70 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 53), (1, 165), (2, 169), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3ce) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.exec (n := 171) (ρ' := [(0, 53), (1, 165), (2, 169), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3d1) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f72 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 53), (1, 165), (2, 172), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3d4) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f73 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 53), (1, 165), (2, 174), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3d8) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.exec (n := 176) (ρ' := [(0, 53), (1, 165), (2, 174), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3db) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f75 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 53), (1, 165), (2, 177), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3de) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f76 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 53), (1, 165), (2, 179), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3e2) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.exec (n := 181) (ρ' := [(0, 53), (1, 165), (2, 179), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3e5) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f78 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 53), (1, 165), (2, 182), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3e8) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f79 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(0, 53), (1, 165), (2, 184), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3ec) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a2f0_4 code

theorem rest_l10a2f0_2 [Bindings] (code : CodeMap) :
    Rest (n := 120) code lifted (codeRange 0x10a2f0 bytes_l10a2f0) [(0, 53), (1, 117), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      50 0x10a36d bytes_l10a2f0_2 b_l10a2f0_2 := by
  have f40 : InstrSpec 0x10a36d [0x89, 0xD1] (fun s => s.RIP = 0x10a36d) (movR32R32Effect 0x10a36d 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10a36d 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x10a36d 0xd1 (by decide)) pre_rip
  have f41 : InstrSpec 0x10a36f [0xC1, 0xE9, 0x10] (fun s => s.RIP = 0x10a36f) (shrR32Effect 0x10a36f 3 1 16)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a36f 3 1 16).toInstrSpec (shr_r32_imm8_effect_step 0x10a36f 0xe9 0x10 (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x10a372 [0x88, 0x4F, 0x0D] (StorePre 0x10a372 3 (fun s => AddrMode.addr (.base 7 (.d8 0xd)) s (0x10a372 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a372 3 1 (.base 7 (.d8 0xd)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a372 3 1 (.base 7 (.d8 0xd))).toInstrSpec (mov_m8_r8_effect_step 0x10a372 1 (by decide) (.base 7 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f43 : InstrSpec 0x10a375 [0x88, 0x77, 0x0E] (StorePre 0x10a375 3 (fun s => AddrMode.addr (.base 7 (.d8 0xe)) s (0x10a375 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a375 3 6 (.base 7 (.d8 0xe)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x10a375 3 6 (.base 7 (.d8 0xe))).toInstrSpec (mov_m8_r8_norex_effect_step 0x10a375 6 (.base 7 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f44 : InstrSpec 0x10a378 [0x88, 0x57, 0x0F] (StorePre 0x10a378 3 (fun s => AddrMode.addr (.base 7 (.d8 0xf)) s (0x10a378 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a378 3 2 (.base 7 (.d8 0xf)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a378 3 2 (.base 7 (.d8 0xf))).toInstrSpec (mov_m8_r8_effect_step 0x10a378 2 (by decide) (.base 7 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x10a37b [0x48, 0x8B, 0x4E, 0x10] (LoadPre 0x10a37b (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10a37b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a37b 1 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10a37b 1 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10a37b 0x48 (by decide) 1 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f46 : InstrSpec 0x10a37f [0x48, 0x0F, 0xC9] (fun s => s.RIP = 0x10a37f) (bswapR64Effect 0x10a37f 3 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR64Effect_footprint 0x10a37f 3 1).toInstrSpec (bswap_r64_effect_step 0x10a37f 0x48 (by decide) 0xc9 (by decide)) pre_rip
  have f47 : InstrSpec 0x10a382 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x10a382) (movR64R64Effect 0x10a382 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a382 2 1).toInstrSpec (mov_r64_r64_effect_step 0x10a382 0x48 0xca (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x10a385 [0x48, 0xC1, 0xEA, 0x38] (fun s => s.RIP = 0x10a385) (shrR64Effect 0x10a385 4 2 56)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a385 4 2 56).toInstrSpec (shr_r64_imm8_effect_step 0x10a385 0x48 0xea 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x10a389 [0x88, 0x57, 0x10] (StorePre 0x10a389 3 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x10a389 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a389 3 2 (.base 7 (.d8 0x10)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a389 3 2 (.base 7 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x10a389 2 (by decide) (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f50 : InstrSpec 0x10a38c [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x10a38c) (movR64R64Effect 0x10a38c 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a38c 2 1).toInstrSpec (mov_r64_r64_effect_step 0x10a38c 0x48 0xca (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x10a38f [0x48, 0xC1, 0xEA, 0x30] (fun s => s.RIP = 0x10a38f) (shrR64Effect 0x10a38f 4 2 48)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a38f 4 2 48).toInstrSpec (shr_r64_imm8_effect_step 0x10a38f 0x48 0xea 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x10a393 [0x88, 0x57, 0x11] (StorePre 0x10a393 3 (fun s => AddrMode.addr (.base 7 (.d8 0x11)) s (0x10a393 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a393 3 2 (.base 7 (.d8 0x11)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a393 3 2 (.base 7 (.d8 0x11))).toInstrSpec (mov_m8_r8_effect_step 0x10a393 2 (by decide) (.base 7 (.d8 0x11)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f53 : InstrSpec 0x10a396 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x10a396) (movR64R64Effect 0x10a396 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a396 2 1).toInstrSpec (mov_r64_r64_effect_step 0x10a396 0x48 0xca (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x10a399 [0x48, 0xC1, 0xEA, 0x28] (fun s => s.RIP = 0x10a399) (shrR64Effect 0x10a399 4 2 40)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a399 4 2 40).toInstrSpec (shr_r64_imm8_effect_step 0x10a399 0x48 0xea 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x10a39d [0x88, 0x57, 0x12] (StorePre 0x10a39d 3 (fun s => AddrMode.addr (.base 7 (.d8 0x12)) s (0x10a39d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a39d 3 2 (.base 7 (.d8 0x12)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a39d 3 2 (.base 7 (.d8 0x12))).toInstrSpec (mov_m8_r8_effect_step 0x10a39d 2 (by decide) (.base 7 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x10a3a0 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x10a3a0) (movR64R64Effect 0x10a3a0 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a3a0 2 1).toInstrSpec (mov_r64_r64_effect_step 0x10a3a0 0x48 0xca (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x10a3a3 [0x48, 0xC1, 0xEA, 0x20] (fun s => s.RIP = 0x10a3a3) (shrR64Effect 0x10a3a3 4 2 32)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a3a3 4 2 32).toInstrSpec (shr_r64_imm8_effect_step 0x10a3a3 0x48 0xea 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x10a3a7 [0x88, 0x57, 0x13] (StorePre 0x10a3a7 3 (fun s => AddrMode.addr (.base 7 (.d8 0x13)) s (0x10a3a7 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3a7 3 2 (.base 7 (.d8 0x13)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a3a7 3 2 (.base 7 (.d8 0x13))).toInstrSpec (mov_m8_r8_effect_step 0x10a3a7 2 (by decide) (.base 7 (.d8 0x13)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f59 : InstrSpec 0x10a3aa [0x89, 0xCA] (fun s => s.RIP = 0x10a3aa) (movR32R32Effect 0x10a3aa 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x10a3aa 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x10a3aa 0xca (by decide)) pre_rip
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f40 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 53), (1, 120), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a36f) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f41 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 53), (1, 122), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a372) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.exec (n := 124) (ρ' := [(0, 53), (1, 122), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a375) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 125) (RestInside.exec (n := 125) (ρ' := [(0, 53), (1, 122), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a378) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 126) (RestInside.exec (n := 126) (ρ' := [(0, 53), (1, 122), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a37b) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f45 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 53), (1, 127), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a37f) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 53), (1, 129), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a382) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f47 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 53), (1, 129), (2, 131), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a385) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f48 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 53), (1, 129), (2, 133), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a389) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.exec (n := 135) (ρ' := [(0, 53), (1, 129), (2, 133), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a38c) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f50 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 53), (1, 129), (2, 136), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a38f) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f51 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 53), (1, 129), (2, 138), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a393) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.exec (n := 140) (ρ' := [(0, 53), (1, 129), (2, 138), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a396) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f53 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 53), (1, 129), (2, 141), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a399) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f54 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 53), (1, 129), (2, 143), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a39d) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.exec (n := 145) (ρ' := [(0, 53), (1, 129), (2, 143), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3a0) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f56 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 53), (1, 129), (2, 146), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3a3) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f57 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 53), (1, 129), (2, 148), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3a7) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.exec (n := 150) (ρ' := [(0, 53), (1, 129), (2, 148), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3aa) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f59 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 53), (1, 129), (2, 151), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3ac) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a2f0_3 code

theorem rest_l10a2f0_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x10a2f0 bytes_l10a2f0) [(0, 53), (1, 57), (2, 86), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      70 0x10a32d bytes_l10a2f0_1 b_l10a2f0_1 := by
  have f20 : InstrSpec 0x10a32d [0x88, 0x57, 0x05] (StorePre 0x10a32d 3 (fun s => AddrMode.addr (.base 7 (.d8 0x5)) s (0x10a32d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a32d 3 2 (.base 7 (.d8 0x5)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a32d 3 2 (.base 7 (.d8 0x5))).toInstrSpec (mov_m8_r8_effect_step 0x10a32d 2 (by decide) (.base 7 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x10a330 [0x48, 0x8B, 0x56, 0x08] (LoadPre 0x10a330 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10a330 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a330 2 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10a330 2 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10a330 0x48 (by decide) 2 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x10a334 [0x48, 0x0F, 0xCA] (fun s => s.RIP = 0x10a334) (bswapR64Effect 0x10a334 3 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR64Effect_footprint 0x10a334 3 2).toInstrSpec (bswap_r64_effect_step 0x10a334 0x48 (by decide) 0xca (by decide)) pre_rip
  have f23 : InstrSpec 0x10a337 [0x88, 0x6F, 0x06] (StorePre 0x10a337 3 (fun s => AddrMode.addr (.base 7 (.d8 0x6)) s (0x10a337 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a337 3 5 (.base 7 (.d8 0x6)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x10a337 3 5 (.base 7 (.d8 0x6))).toInstrSpec (mov_m8_r8_norex_effect_step 0x10a337 5 (.base 7 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x10a33a [0x88, 0x4F, 0x07] (StorePre 0x10a33a 3 (fun s => AddrMode.addr (.base 7 (.d8 0x7)) s (0x10a33a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a33a 3 1 (.base 7 (.d8 0x7)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a33a 3 1 (.base 7 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x10a33a 1 (by decide) (.base 7 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x10a33d [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x10a33d) (movR64R64Effect 0x10a33d 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10a33d 1 2).toInstrSpec (mov_r64_r64_effect_step 0x10a33d 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10a340 [0x48, 0xC1, 0xE9, 0x38] (fun s => s.RIP = 0x10a340) (shrR64Effect 0x10a340 4 1 56)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a340 4 1 56).toInstrSpec (shr_r64_imm8_effect_step 0x10a340 0x48 0xe9 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x10a344 [0x88, 0x4F, 0x08] (StorePre 0x10a344 3 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10a344 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a344 3 1 (.base 7 (.d8 0x8)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a344 3 1 (.base 7 (.d8 0x8))).toInstrSpec (mov_m8_r8_effect_step 0x10a344 1 (by decide) (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x10a347 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x10a347) (movR64R64Effect 0x10a347 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10a347 1 2).toInstrSpec (mov_r64_r64_effect_step 0x10a347 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x10a34a [0x48, 0xC1, 0xE9, 0x30] (fun s => s.RIP = 0x10a34a) (shrR64Effect 0x10a34a 4 1 48)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a34a 4 1 48).toInstrSpec (shr_r64_imm8_effect_step 0x10a34a 0x48 0xe9 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10a34e [0x88, 0x4F, 0x09] (StorePre 0x10a34e 3 (fun s => AddrMode.addr (.base 7 (.d8 0x9)) s (0x10a34e + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a34e 3 1 (.base 7 (.d8 0x9)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a34e 3 1 (.base 7 (.d8 0x9))).toInstrSpec (mov_m8_r8_effect_step 0x10a34e 1 (by decide) (.base 7 (.d8 0x9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x10a351 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x10a351) (movR64R64Effect 0x10a351 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10a351 1 2).toInstrSpec (mov_r64_r64_effect_step 0x10a351 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10a354 [0x48, 0xC1, 0xE9, 0x28] (fun s => s.RIP = 0x10a354) (shrR64Effect 0x10a354 4 1 40)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a354 4 1 40).toInstrSpec (shr_r64_imm8_effect_step 0x10a354 0x48 0xe9 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x10a358 [0x88, 0x4F, 0x0A] (StorePre 0x10a358 3 (fun s => AddrMode.addr (.base 7 (.d8 0xa)) s (0x10a358 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a358 3 1 (.base 7 (.d8 0xa)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a358 3 1 (.base 7 (.d8 0xa))).toInstrSpec (mov_m8_r8_effect_step 0x10a358 1 (by decide) (.base 7 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x10a35b [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x10a35b) (movR64R64Effect 0x10a35b 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10a35b 1 2).toInstrSpec (mov_r64_r64_effect_step 0x10a35b 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x10a35e [0x48, 0xC1, 0xE9, 0x20] (fun s => s.RIP = 0x10a35e) (shrR64Effect 0x10a35e 4 1 32)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a35e 4 1 32).toInstrSpec (shr_r64_imm8_effect_step 0x10a35e 0x48 0xe9 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x10a362 [0x88, 0x4F, 0x0B] (StorePre 0x10a362 3 (fun s => AddrMode.addr (.base 7 (.d8 0xb)) s (0x10a362 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a362 3 1 (.base 7 (.d8 0xb)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a362 3 1 (.base 7 (.d8 0xb))).toInstrSpec (mov_m8_r8_effect_step 0x10a362 1 (by decide) (.base 7 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x10a365 [0x89, 0xD1] (fun s => s.RIP = 0x10a365) (movR32R32Effect 0x10a365 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10a365 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x10a365 0xd1 (by decide)) pre_rip
  have f38 : InstrSpec 0x10a367 [0xC1, 0xE9, 0x18] (fun s => s.RIP = 0x10a367) (shrR32Effect 0x10a367 3 1 24)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a367 3 1 24).toInstrSpec (shr_r32_imm8_effect_step 0x10a367 0xe9 0x18 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10a36a [0x88, 0x4F, 0x0C] (StorePre 0x10a36a 3 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x10a36a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a36a 3 1 (.base 7 (.d8 0xc)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a36a 3 1 (.base 7 (.d8 0xc))).toInstrSpec (mov_m8_r8_effect_step 0x10a36a 1 (by decide) (.base 7 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 53), (1, 57), (2, 86), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a330) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f21 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 53), (1, 57), (2, 89), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a334) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 53), (1, 57), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a337) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 53), (1, 57), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a33a) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 53), (1, 57), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a33d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f25 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 53), (1, 95), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a340) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 53), (1, 97), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a344) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 53), (1, 97), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a347) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f28 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 53), (1, 100), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a34a) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f29 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 53), (1, 102), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a34e) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 53), (1, 102), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a351) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f31 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 53), (1, 105), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a354) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f32 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 53), (1, 107), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a358) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.exec (n := 109) (ρ' := [(0, 53), (1, 107), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a35b) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f34 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 53), (1, 110), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a35e) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f35 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 53), (1, 112), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a362) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.exec (n := 114) (ρ' := [(0, 53), (1, 112), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a365) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f37 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 53), (1, 115), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a367) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f38 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 53), (1, 117), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a36a) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.exec (n := 119) (ρ' := [(0, 53), (1, 117), (2, 91), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a36d) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10a2f0_2 code

theorem rest_l10a2f0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a2f0 bytes_l10a2f0) (entryMap (live .l10a2f0))
      90 0x10a2f0 bytes_l10a2f0 b_l10a2f0 := by
  have f0 : InstrSpec 0x10a2f0 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x10a2f0) (movR64R64Effect 0x10a2f0 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10a2f0 0 7).toInstrSpec (mov_r64_r64_effect_step 0x10a2f0 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10a2f3 [0x48, 0x8B, 0x0E] (LoadPre 0x10a2f3 (fun s => AddrMode.addr (.base 6 .none) s (0x10a2f3 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a2f3 1 (.base 6 .none))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10a2f3 1 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10a2f3 0x48 (by decide) 1 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10a2f6 [0x48, 0x0F, 0xC9] (fun s => s.RIP = 0x10a2f6) (bswapR64Effect 0x10a2f6 3 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR64Effect_footprint 0x10a2f6 3 1).toInstrSpec (bswap_r64_effect_step 0x10a2f6 0x48 (by decide) 0xc9 (by decide)) pre_rip
  have f3 : InstrSpec 0x10a2f9 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x10a2f9) (movR64R64Effect 0x10a2f9 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a2f9 2 1).toInstrSpec (mov_r64_r64_effect_step 0x10a2f9 0x48 0xca (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10a2fc [0x48, 0xC1, 0xEA, 0x38] (fun s => s.RIP = 0x10a2fc) (shrR64Effect 0x10a2fc 4 2 56)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a2fc 4 2 56).toInstrSpec (shr_r64_imm8_effect_step 0x10a2fc 0x48 0xea 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10a300 [0x88, 0x17] (StorePre 0x10a300 2 (fun s => AddrMode.addr (.base 7 .none) s (0x10a300 + BitVec.ofNat 64 2)) 1) (movM8R8Effect 0x10a300 2 2 (.base 7 .none))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a300 2 2 (.base 7 .none)).toInstrSpec (mov_m8_r8_effect_step 0x10a300 2 (by decide) (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10a302 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x10a302) (movR64R64Effect 0x10a302 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a302 2 1).toInstrSpec (mov_r64_r64_effect_step 0x10a302 0x48 0xca (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10a305 [0x48, 0xC1, 0xEA, 0x30] (fun s => s.RIP = 0x10a305) (shrR64Effect 0x10a305 4 2 48)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a305 4 2 48).toInstrSpec (shr_r64_imm8_effect_step 0x10a305 0x48 0xea 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10a309 [0x88, 0x57, 0x01] (StorePre 0x10a309 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1)) s (0x10a309 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a309 3 2 (.base 7 (.d8 0x1)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a309 3 2 (.base 7 (.d8 0x1))).toInstrSpec (mov_m8_r8_effect_step 0x10a309 2 (by decide) (.base 7 (.d8 0x1)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10a30c [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x10a30c) (movR64R64Effect 0x10a30c 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a30c 2 1).toInstrSpec (mov_r64_r64_effect_step 0x10a30c 0x48 0xca (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10a30f [0x48, 0xC1, 0xEA, 0x28] (fun s => s.RIP = 0x10a30f) (shrR64Effect 0x10a30f 4 2 40)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a30f 4 2 40).toInstrSpec (shr_r64_imm8_effect_step 0x10a30f 0x48 0xea 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10a313 [0x88, 0x57, 0x02] (StorePre 0x10a313 3 (fun s => AddrMode.addr (.base 7 (.d8 0x2)) s (0x10a313 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a313 3 2 (.base 7 (.d8 0x2)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a313 3 2 (.base 7 (.d8 0x2))).toInstrSpec (mov_m8_r8_effect_step 0x10a313 2 (by decide) (.base 7 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10a316 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x10a316) (movR64R64Effect 0x10a316 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a316 2 1).toInstrSpec (mov_r64_r64_effect_step 0x10a316 0x48 0xca (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10a319 [0x48, 0xC1, 0xEA, 0x20] (fun s => s.RIP = 0x10a319) (shrR64Effect 0x10a319 4 2 32)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a319 4 2 32).toInstrSpec (shr_r64_imm8_effect_step 0x10a319 0x48 0xea 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10a31d [0x88, 0x57, 0x03] (StorePre 0x10a31d 3 (fun s => AddrMode.addr (.base 7 (.d8 0x3)) s (0x10a31d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a31d 3 2 (.base 7 (.d8 0x3)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a31d 3 2 (.base 7 (.d8 0x3))).toInstrSpec (mov_m8_r8_effect_step 0x10a31d 2 (by decide) (.base 7 (.d8 0x3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x10a320 [0x89, 0xCA] (fun s => s.RIP = 0x10a320) (movR32R32Effect 0x10a320 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x10a320 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x10a320 0xca (by decide)) pre_rip
  have f16 : InstrSpec 0x10a322 [0xC1, 0xEA, 0x18] (fun s => s.RIP = 0x10a322) (shrR32Effect 0x10a322 3 2 24)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a322 3 2 24).toInstrSpec (shr_r32_imm8_effect_step 0x10a322 0xea 0x18 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10a325 [0x88, 0x57, 0x04] (StorePre 0x10a325 3 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x10a325 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a325 3 2 (.base 7 (.d8 0x4)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a325 3 2 (.base 7 (.d8 0x4))).toInstrSpec (mov_m8_r8_effect_step 0x10a325 2 (by decide) (.base 7 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x10a328 [0x89, 0xCA] (fun s => s.RIP = 0x10a328) (movR32R32Effect 0x10a328 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x10a328 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x10a328 0xca (by decide)) pre_rip
  have f19 : InstrSpec 0x10a32a [0xC1, 0xEA, 0x10] (fun s => s.RIP = 0x10a32a) (shrR32Effect 0x10a32a 3 2 16)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a32a 3 2 16).toInstrSpec (shr_r32_imm8_effect_step 0x10a32a 0xea 0x10 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2f3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2f6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2f9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2fc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 57), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a300) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 57), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a302) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 57), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a305) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 57), (2, 66), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a309) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 57), (2, 66), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a30c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 57), (2, 69), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a30f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 57), (2, 71), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a313) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 57), (2, 71), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a316) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 57), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a319) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 53), (1, 57), (2, 76), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a31d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 57), (2, 76), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a320) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 53), (1, 57), (2, 79), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a322) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 53), (1, 57), (2, 81), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a325) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 53), (1, 57), (2, 81), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a328) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 53), (1, 57), (2, 84), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a32a) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f19 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 53), (1, 57), (2, 86), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a32d) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a2f0_1 code

theorem block_l10a2f0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a2f0 :=
  Rest.liftedBlock (rest_l10a2f0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a2f0 x hx)

theorem rest_l10fa10_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x10fa10 bytes_l10fa10) [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 86), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 84), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      5 0x10fa54 bytes_l10fa10_1 b_l10fa10_1 := by
  have f20 : InstrSpec 0x10fa54 [0x4C, 0x8B, 0x76, 0x10] (LoadPre 0x10fa54 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10fa54 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa54 14 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x10fa54 14 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10fa54 0x4c (by decide) 6 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x10fa58 [0x4C, 0x8B, 0x7E, 0x18] (LoadPre 0x10fa58 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10fa58 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa58 15 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10fa58 15 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10fa58 0x4c (by decide) 7 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x10fa5c [0x4C, 0x8B, 0x66, 0x20] (LoadPre 0x10fa5c (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x10fa5c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa5c 12 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x10fa5c 12 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10fa5c 0x4c (by decide) 4 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x10fa60 [0x8B, 0x7E, 0x50] (LoadPre 0x10fa60 (fun s => AddrMode.addr (.base 6 (.d8 0x50)) s (0x10fa60 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x10fa60 7 (.base 6 (.d8 0x50)))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x10fa60 7 (.base 6 (.d8 0x50))).toInstrSpec (mov_r32_m32_low_effect_step 0x10fa60 7 (.base 6 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x10fa63 [0xE8, 0xE8, 0x82, 0x01, 0x00] (PushPre 0x10fa63 5) (callEffect (fun _ => 0x127d50) 0x10fa68)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10fa63 0x127d50 0x10fa68).toInstrSpec (call_rel32_effect_step 0x10fa63 0x182e8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f20 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 86), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 84), (14, 88), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa58) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f21 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 86), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 84), (14, 88), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa5c) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f22 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 86), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 92), (13, 84), (14, 88), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa60) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f23 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 86), (6, 6), (7, 94), (8, 8), (9, 9), (10, 10), (11, 11), (12, 92), (13, 84), (14, 88), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa63) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f24 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 96), (5, 86), (6, 6), (7, 94), (8, 8), (9, 9), (10, 10), (11, 11), (12, 92), (13, 84), (14, 88), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f24 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 98) (by decide) (by decide) rfl rfl

theorem rest_l10fa10 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fa10 bytes_l10fa10) (entryMap (live .l10fa10))
      25 0x10fa10 bytes_l10fa10 b_l10fa10 := by
  have f0 : InstrSpec 0x10fa10 [0x55] (PushPre 0x10fa10 1) (pushR64Effect 0x10fa10 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fa10 1 5).toInstrSpec (push_r64_effect_step 0x10fa10 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10fa11 [0x41, 0x57] (PushPre 0x10fa11 2) (pushR64Effect 0x10fa11 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fa11 2 15).toInstrSpec (push_r64_rex_effect_step 0x10fa11 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x10fa13 [0x41, 0x56] (PushPre 0x10fa13 2) (pushR64Effect 0x10fa13 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fa13 2 14).toInstrSpec (push_r64_rex_effect_step 0x10fa13 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10fa15 [0x41, 0x55] (PushPre 0x10fa15 2) (pushR64Effect 0x10fa15 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fa15 2 13).toInstrSpec (push_r64_rex_effect_step 0x10fa15 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10fa17 [0x41, 0x54] (PushPre 0x10fa17 2) (pushR64Effect 0x10fa17 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fa17 2 12).toInstrSpec (push_r64_rex_effect_step 0x10fa17 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10fa19 [0x53] (PushPre 0x10fa19 1) (pushR64Effect 0x10fa19 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fa19 1 3).toInstrSpec (push_r64_effect_step 0x10fa19 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10fa1a [0x48, 0x83, 0xEC, 0x28] (fun s => s.RIP = 0x10fa1a) (subR64Imm8Effect 0x10fa1a 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10fa1a 4 0x28).toInstrSpec (sub_r64_imm8_effect_step 0x10fa1a 0x48 0xec 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10fa1e [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x10fa1e) (movR64R64Effect 0x10fa1e 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10fa1e 3 7).toInstrSpec (mov_r64_r64_effect_step 0x10fa1e 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10fa21 [0x48, 0x8B, 0x46, 0x28] (LoadPre 0x10fa21 (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x10fa21 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa21 0 (.base 6 (.d8 0x28)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fa21 0 (.base 6 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10fa21 0x48 (by decide) 0 (.base 6 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10fa25 [0x48, 0x89, 0x04, 0x24] (StorePre 0x10fa25 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fa25 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fa25 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fa25 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10fa25 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10fa29 [0x48, 0x8B, 0x46, 0x30] (LoadPre 0x10fa29 (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x10fa29 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa29 0 (.base 6 (.d8 0x30)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fa29 0 (.base 6 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10fa29 0x48 (by decide) 0 (.base 6 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10fa2d [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x10fa2d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10fa2d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fa2d 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fa2d 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10fa2d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10fa32 [0x48, 0x8B, 0x46, 0x38] (LoadPre 0x10fa32 (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x10fa32 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa32 0 (.base 6 (.d8 0x38)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fa32 0 (.base 6 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10fa32 0x48 (by decide) 0 (.base 6 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10fa36 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x10fa36 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10fa36 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fa36 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fa36 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10fa36 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x10fa3b [0x48, 0x8B, 0x46, 0x40] (LoadPre 0x10fa3b (fun s => AddrMode.addr (.base 6 (.d8 0x40)) s (0x10fa3b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa3b 0 (.base 6 (.d8 0x40)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fa3b 0 (.base 6 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10fa3b 0x48 (by decide) 0 (.base 6 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x10fa3f [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x10fa3f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10fa3f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fa3f 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fa3f 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10fa3f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x10fa44 [0x48, 0x8B, 0x46, 0x48] (LoadPre 0x10fa44 (fun s => AddrMode.addr (.base 6 (.d8 0x48)) s (0x10fa44 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa44 0 (.base 6 (.d8 0x48)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fa44 0 (.base 6 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10fa44 0x48 (by decide) 0 (.base 6 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10fa48 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x10fa48 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10fa48 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fa48 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fa48 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10fa48 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x10fa4d [0x4C, 0x8B, 0x2E] (LoadPre 0x10fa4d (fun s => AddrMode.addr (.base 6 .none) s (0x10fa4d + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10fa4d 13 (.base 6 .none))
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x10fa4d 13 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10fa4d 0x4c (by decide) 5 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x10fa50 [0x48, 0x8B, 0x6E, 0x08] (LoadPre 0x10fa50 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10fa50 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa50 5 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x10fa50 5 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10fa50 0x48 (by decide) 5 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa11) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa13) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa15) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa17) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa19) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa1a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa1e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa21) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa25) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa29) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa2d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa32) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa36) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa3b) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa3f) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa44) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa48) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa4d) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f18 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 84), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa50) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f19 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 86), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 84), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa54) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10fa10_1 code

theorem block_l10fa10 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fa10 :=
  Rest.liftedBlock (rest_l10fa10 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fa10 x hx)

theorem rest_l10fa68_2 [Bindings] (code : CodeMap) :
    Rest (n := 118) code lifted (codeRange 0x10fa68 bytes_l10fa68) [(0, 114), (1, 97), (2, 81), (3, 3), (4, 116), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]
      7 0x10fb08 bytes_l10fa68_2 b_l10fa68_2 := by
  have f40 : InstrSpec 0x10fb08 [0x5B] (PopPre 0x10fb08) (popR64Effect 0x10fb08 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fb08 1 3).toInstrSpec (pop_r64_effect_step 0x10fb08 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f41 : InstrSpec 0x10fb09 [0x41, 0x5C] (PopPre 0x10fb09) (popR64Effect 0x10fb09 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fb09 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10fb09 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f42 : InstrSpec 0x10fb0b [0x41, 0x5D] (PopPre 0x10fb0b) (popR64Effect 0x10fb0b 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fb0b 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10fb0b 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f43 : InstrSpec 0x10fb0d [0x41, 0x5E] (PopPre 0x10fb0d) (popR64Effect 0x10fb0d 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fb0d 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10fb0d 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f44 : InstrSpec 0x10fb0f [0x41, 0x5F] (PopPre 0x10fb0f) (popR64Effect 0x10fb0f 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fb0f 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10fb0f 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f45 : InstrSpec 0x10fb11 [0x5D] (PopPre 0x10fb11) (popR64Effect 0x10fb11 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fb11 1 5).toInstrSpec (pop_r64_effect_step 0x10fb11 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f46 : InstrSpec 0x10fb12 [0xC3] (RetPre 0x10fb12) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10fb12).toInstrSpec (ret_effect_step 0x10fb12) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f40 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 119) f40 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 120) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 118), (4, 119), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb09) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f41 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 122) f41 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 123) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 118), (4, 122), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 121), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb0b) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f42 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 125) f42 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 126) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 118), (4, 125), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 121), (13, 124), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb0d) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f43 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 128) f43 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 129) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 118), (4, 128), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 121), (13, 124), (14, 127), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb0f) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f44 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 131) f44 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 132) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 118), (4, 131), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 121), (13, 124), (14, 127), (15, 130), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb11) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f45 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 134) f45 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 135) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 118), (4, 134), (5, 133), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 121), (13, 124), (14, 127), (15, 130), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb12) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f46 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 137) f46 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 138) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 118), (4, 137), (5, 133), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 121), (13, 124), (14, 127), (15, 130), (22, 22), (39, 39), (50, 50), (51, 51)]) f46 (by decide) rfl rfl rfl (by decide)

theorem rest_l10fa68_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x10fa68 bytes_l10fa68) [(0, 69), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]
      27 0x10faab bytes_l10fa68_1 b_l10fa68_1 := by
  have f20 : InstrSpec 0x10faab [0x49, 0x21, 0xC0] (fun s => s.RIP = 0x10faab) (andR64R64Effect 0x10faab 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10faab 8 0).toInstrSpec (and_r64_r64_effect_step 0x10faab 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x10faae [0x48, 0x23, 0x44, 0x24, 0x20] (LoadPre 0x10faae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10faae + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x10faae 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (andR64M64Effect_footprint 0x10faae 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (and_r64_m64_effect_step 0x10faae 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x10fab3 [0x83, 0xE1, 0x01] (fun s => s.RIP = 0x10fab3) (andR32Imm8Effect 0x10fab3 3 1 0x1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x10fab3 3 1 0x1).toInstrSpec (and_r32_imm8_effect_step 0x10fab3 0xe1 0x1 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x10fab6 [0x4C, 0x89, 0x2B] (StorePre 0x10fab6 3 (fun s => AddrMode.addr (.base 3 .none) s (0x10fab6 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10fab6 13 (.base 3 .none))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fab6 13 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10fab6 0x4c (by decide) 5 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x10fab9 [0x48, 0x89, 0x6B, 0x08] (StorePre 0x10fab9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10fab9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fab9 5 (.base 3 (.d8 0x8)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fab9 5 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10fab9 0x48 (by decide) 5 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x10fabd [0x4C, 0x89, 0x73, 0x10] (StorePre 0x10fabd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10fabd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fabd 14 (.base 3 (.d8 0x10)))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fabd 14 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10fabd 0x4c (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x10fac1 [0x4C, 0x89, 0x7B, 0x18] (StorePre 0x10fac1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x10fac1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fac1 15 (.base 3 (.d8 0x18)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fac1 15 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10fac1 0x4c (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x10fac5 [0x4C, 0x89, 0x63, 0x20] (StorePre 0x10fac5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x10fac5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fac5 12 (.base 3 (.d8 0x20)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fac5 12 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10fac5 0x4c (by decide) 4 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x10fac9 [0x48, 0x89, 0x53, 0x28] (StorePre 0x10fac9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x10fac9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fac9 2 (.base 3 (.d8 0x28)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fac9 2 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10fac9 0x48 (by decide) 2 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x10facd [0x48, 0x89, 0x73, 0x30] (StorePre 0x10facd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x10facd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10facd 6 (.base 3 (.d8 0x30)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10facd 6 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10facd 0x48 (by decide) 6 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x10fad1 [0x48, 0x89, 0x7B, 0x38] (StorePre 0x10fad1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x10fad1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fad1 7 (.base 3 (.d8 0x38)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fad1 7 (.base 3 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10fad1 0x48 (by decide) 7 (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x10fad5 [0x4C, 0x89, 0x43, 0x40] (StorePre 0x10fad5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x10fad5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fad5 8 (.base 3 (.d8 0x40)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fad5 8 (.base 3 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x10fad5 0x4c (by decide) 0 (.base 3 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x10fad9 [0x48, 0x89, 0x43, 0x48] (StorePre 0x10fad9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x48)) s (0x10fad9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fad9 0 (.base 3 (.d8 0x48)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fad9 0 (.base 3 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x10fad9 0x48 (by decide) 0 (.base 3 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x10fadd [0x48, 0x89, 0x4B, 0x50] (StorePre 0x10fadd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x10fadd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fadd 1 (.base 3 (.d8 0x50)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fadd 1 (.base 3 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x10fadd 0x48 (by decide) 1 (.base 3 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x10fae1 [0x48, 0xC7, 0x43, 0x58, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10fae1 8 (fun s => AddrMode.addr (.base 3 (.d8 0x58)) s (0x10fae1 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10fae1 (.base 3 (.d8 0x58)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10fae1 (.base 3 (.d8 0x58)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10fae1 0x48 (by decide) (.base 3 (.d8 0x58)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x10fae9 [0x48, 0xC7, 0x43, 0x60, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10fae9 8 (fun s => AddrMode.addr (.base 3 (.d8 0x60)) s (0x10fae9 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10fae9 (.base 3 (.d8 0x60)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10fae9 (.base 3 (.d8 0x60)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10fae9 0x48 (by decide) (.base 3 (.d8 0x60)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x10faf1 [0x48, 0xC7, 0x43, 0x68, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10faf1 8 (fun s => AddrMode.addr (.base 3 (.d8 0x68)) s (0x10faf1 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10faf1 (.base 3 (.d8 0x68)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10faf1 (.base 3 (.d8 0x68)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10faf1 0x48 (by decide) (.base 3 (.d8 0x68)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x10faf9 [0x48, 0xC7, 0x43, 0x70, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10faf9 8 (fun s => AddrMode.addr (.base 3 (.d8 0x70)) s (0x10faf9 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10faf9 (.base 3 (.d8 0x70)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10faf9 (.base 3 (.d8 0x70)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10faf9 0x48 (by decide) (.base 3 (.d8 0x70)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x10fb01 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10fb01) (movR64R64Effect 0x10fb01 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10fb01 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10fb01 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10fb04 [0x48, 0x83, 0xC4, 0x28] (fun s => s.RIP = 0x10fb04) (addR64Imm8Effect 0x10fb04 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10fb04 4 0x28).toInstrSpec (add_r64_imm8_effect_step 0x10fb04 0x48 0xc4 0x28 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 69), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10faae) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fab3) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fab6) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fab9) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fabd) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fac1) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.exec (n := 102) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fac5) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 103) (RestInside.exec (n := 103) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fac9) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10facd) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.exec (n := 105) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fad1) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fad5) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fad9) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 108) (RestInside.exec (n := 108) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fadd) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 109) (RestInside.exec (n := 109) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fae1) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 110) (RestInside.exec (n := 110) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fae9) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 111) (RestInside.exec (n := 111) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10faf1) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 112) (RestInside.exec (n := 112) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10faf9) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 113) (RestInside.exec (n := 113) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb01) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f38 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb04) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f39 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 3), (4, 116), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb08) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10fa68_2 code

theorem rest_l10fa68 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fa68 bytes_l10fa68) (entryMap (live .l10fa68))
      47 0x10fa68 bytes_l10fa68 b_l10fa68 := by
  have f0 : InstrSpec 0x10fa68 [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x10fa68) (movzxR32R8Effect 0x10fa68 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x10fa68 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x10fa68 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10fa6b [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10fa6b) (movR64R64Effect 0x10fa6b 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10fa6b 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10fa6b 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10fa6e [0x48, 0xF7, 0xD9] (fun s => s.RIP = 0x10fa6e) (negR64Effect 0x10fa6e 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR64Effect_footprint 0x10fa6e 1).toInstrSpec (neg_r64_effect_step 0x10fa6e 0x48 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10fa71 [0x48, 0x8B, 0x34, 0x24] (LoadPre 0x10fa71 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fa71 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa71 6 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10fa71 6 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10fa71 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10fa75 [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x10fa75) (movR64R64Effect 0x10fa75 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10fa75 2 6).toInstrSpec (mov_r64_r64_effect_step 0x10fa75 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10fa78 [0x48, 0x83, 0xF2, 0x01] (fun s => s.RIP = 0x10fa78) (xorR64Imm8Effect 0x10fa78 2 0x1)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR64Imm8Effect_footprint 0x10fa78 2 0x1).toInstrSpec (xor_r64_imm8_effect_step 0x10fa78 0x48 0xf2 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10fa7c [0x48, 0x21, 0xCA] (fun s => s.RIP = 0x10fa7c) (andR64R64Effect 0x10fa7c 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fa7c 2 1).toInstrSpec (and_r64_r64_effect_step 0x10fa7c 0x48 0xca (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10fa7f [0xF7, 0xD1] (fun s => s.RIP = 0x10fa7f) (notR32Effect 0x10fa7f 2 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR32Effect_footprint 0x10fa7f 2 1).toInstrSpec (not_r32_effect_step 0x10fa7f 0xd1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10fa81 [0x48, 0xFF, 0xC8] (fun s => s.RIP = 0x10fa81) (decR64Effect 0x10fa81 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (decR64Effect_footprint 0x10fa81 0).toInstrSpec (dec_r64_effect_step 0x10fa81 0x48 0xc8 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10fa84 [0x49, 0x21, 0xC5] (fun s => s.RIP = 0x10fa84) (andR64R64Effect 0x10fa84 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fa84 13 0).toInstrSpec (and_r64_r64_effect_step 0x10fa84 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10fa87 [0x48, 0x21, 0xC5] (fun s => s.RIP = 0x10fa87) (andR64R64Effect 0x10fa87 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fa87 5 0).toInstrSpec (and_r64_r64_effect_step 0x10fa87 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10fa8a [0x49, 0x21, 0xC6] (fun s => s.RIP = 0x10fa8a) (andR64R64Effect 0x10fa8a 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fa8a 14 0).toInstrSpec (and_r64_r64_effect_step 0x10fa8a 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10fa8d [0x49, 0x21, 0xC7] (fun s => s.RIP = 0x10fa8d) (andR64R64Effect 0x10fa8d 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fa8d 15 0).toInstrSpec (and_r64_r64_effect_step 0x10fa8d 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10fa90 [0x49, 0x21, 0xC4] (fun s => s.RIP = 0x10fa90) (andR64R64Effect 0x10fa90 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fa90 12 0).toInstrSpec (and_r64_r64_effect_step 0x10fa90 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10fa93 [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x10fa93) (xorR64R64Effect 0x10fa93 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fa93 2 6).toInstrSpec (xor_r64_r64_effect_step 0x10fa93 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10fa96 [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x10fa96 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10fa96 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10fa96 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10fa96 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10fa96 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10fa9b [0x48, 0x21, 0xC6] (fun s => s.RIP = 0x10fa9b) (andR64R64Effect 0x10fa9b 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fa9b 6 0).toInstrSpec (and_r64_r64_effect_step 0x10fa9b 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10fa9e [0x48, 0x8B, 0x7C, 0x24, 0x10] (LoadPre 0x10fa9e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10fa9e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10fa9e 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10fa9e 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10fa9e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x10faa3 [0x48, 0x21, 0xC7] (fun s => s.RIP = 0x10faa3) (andR64R64Effect 0x10faa3 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10faa3 7 0).toInstrSpec (and_r64_r64_effect_step 0x10faa3 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x10faa6 [0x4C, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x10faa6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10faa6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10faa6 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10faa6 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10faa6 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa6b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa6e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa71) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa75) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 57), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa78) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 57), (2, 63), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa7c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 57), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa7f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 67), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa81) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 67), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa84) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 67), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa87) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 69), (1, 67), (2, 65), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa8a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 69), (1, 67), (2, 65), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa8d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 69), (1, 67), (2, 65), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa90) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 69), (1, 67), (2, 65), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa93) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 69), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa96) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 69), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 83), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa9b) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 69), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa9e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 69), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 87), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10faa3) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 69), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10faa6) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 69), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10faab) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10fa68_1 code

theorem block_l10fa68 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fa68 :=
  Rest.liftedBlock (rest_l10fa68 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fa68 x hx)

theorem rest_l10fe50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fe50 bytes_l10fe50) (entryMap (live .l10fe50))
      1 0x10fe50 bytes_l10fe50 b_l10fe50 := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x10fe50 0xffffee8b (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10fe50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fe50 :=
  Rest.liftedBlock (rest_l10fe50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fe50 x hx)

theorem rest_l10ff00 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10ff00 bytes_l10ff00) (entryMap (live .l10ff00))
      11 0x10ff00 bytes_l10ff00 b_l10ff00 := by
  have f0 : InstrSpec 0x10ff00 [0x55] (PushPre 0x10ff00 1) (pushR64Effect 0x10ff00 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ff00 1 5).toInstrSpec (push_r64_effect_step 0x10ff00 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10ff01 [0x41, 0x57] (PushPre 0x10ff01 2) (pushR64Effect 0x10ff01 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ff01 2 15).toInstrSpec (push_r64_rex_effect_step 0x10ff01 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x10ff03 [0x41, 0x56] (PushPre 0x10ff03 2) (pushR64Effect 0x10ff03 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ff03 2 14).toInstrSpec (push_r64_rex_effect_step 0x10ff03 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10ff05 [0x41, 0x55] (PushPre 0x10ff05 2) (pushR64Effect 0x10ff05 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ff05 2 13).toInstrSpec (push_r64_rex_effect_step 0x10ff05 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10ff07 [0x41, 0x54] (PushPre 0x10ff07 2) (pushR64Effect 0x10ff07 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ff07 2 12).toInstrSpec (push_r64_rex_effect_step 0x10ff07 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10ff09 [0x53] (PushPre 0x10ff09 1) (pushR64Effect 0x10ff09 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ff09 1 3).toInstrSpec (push_r64_effect_step 0x10ff09 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10ff0a [0x48, 0x81, 0xEC, 0x48, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10ff0a) (subR64Imm32Effect 0x10ff0a 4 0x148)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10ff0a 4 0x148).toInstrSpec (sub_r64_imm32_effect_step 0x10ff0a 0x48 0xec 0x148 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10ff11 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x10ff11) (movR64R64Effect 0x10ff11 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10ff11 3 7).toInstrSpec (mov_r64_r64_effect_step 0x10ff11 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10ff14 [0x4C, 0x8D, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ff14) (leaR64Effect 0x10ff14 14 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x10ff14 14 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (lea_r64_effect_step 0x10ff14 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10ff1c [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10ff1c) (movR64R64Effect 0x10ff1c 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10ff1c 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10ff1c 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10ff1f [0xE8, 0x0C, 0x10, 0x01, 0x00] (PushPre 0x10ff1f 5) (callEffect (fun _ => 0x120f30) 0x10ff24)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10ff1f 0x120f30 0x10ff24).toInstrSpec (call_rel32_effect_step 0x10ff1f 0x1100c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff01) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff03) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff05) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff07) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff09) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff0a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff11) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff14) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff1c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff1f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (3, 67), (4, 73), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f30) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l10ff00 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10ff00 :=
  Rest.liftedBlock (rest_l10ff00 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10ff00 x hx)

theorem rest_l10ff24 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10ff24 bytes_l10ff24) (entryMap (live .l10ff24))
      11 0x10ff24 bytes_l10ff24 b_l10ff24 := by
  have f0 : InstrSpec 0x10ff24 [0x48, 0x8D, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ff24) (leaR64Effect 0x10ff24 0 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x10ff24 0 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (lea_r64_effect_step 0x10ff24 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10ff2c [0xB9, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ff2c) (movR32Imm32Effect 0x10ff2c 5 1 0xb)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10ff2c 5 1 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x10ff2c 0xb9 (by decide) 0xb) pre_rip
  have f2 : InstrSpec 0x10ff31 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x10ff31) (movR64R64Effect 0x10ff31 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10ff31 7 0).toInstrSpec (mov_r64_r64_effect_step 0x10ff31 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10ff34 [0x48, 0xC7, 0xC6, 0x70, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x10ff34) (movR64Imm32Effect 0x10ff34 6 0x202b70)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10ff34 6 0x202b70).toInstrSpec (mov_r64_imm32_effect_step 0x10ff34 0x48 0xc6 (by decide) (by decide) (by decide) 0x202b70) pre_rip
  have f4 : InstrSpec 0x10ff3b [0xF3, 0x48, 0xA5] (RepPre 0x10ff3b (RepMovsqPre 0x10ff3b)) (repMovsqEffect 0x10ff3b)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10ff3b).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10ff3b 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x10ff3e [0x8B, 0x8C, 0x24, 0xE8, 0x00, 0x00, 0x00] (LoadPre 0x10ff3e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10ff3e + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x10ff3e 1 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x10ff3e 1 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_r32_m32_low_effect_step 0x10ff3e 1 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10ff45 [0x89, 0x4C, 0x24, 0x0C] (StorePre 0x10ff45 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x10ff45 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10ff45 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10ff45 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x10ff45 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10ff49 [0x48, 0x8D, 0x7C, 0x24, 0x38] (fun s => s.RIP = 0x10ff49) (leaR64Effect 0x10ff49 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10ff49 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x10ff49 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10ff4e [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x10ff4e) (movR64R64Effect 0x10ff4e 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10ff4e 6 0).toInstrSpec (mov_r64_r64_effect_step 0x10ff4e 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10ff51 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x10ff51) (movR64R64Effect 0x10ff51 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10ff51 2 14).toInstrSpec (mov_r64_r64_effect_step 0x10ff51 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10ff54 [0xE8, 0x17, 0x05, 0x01, 0x00] (PushPre 0x10ff54 5) (callEffect (fun _ => 0x120470) 0x10ff59)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10ff54 0x120470 0x10ff59).toInstrSpec (call_rel32_effect_step 0x10ff54 0x10517 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff2c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff31) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff34) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff3b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff3e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff45) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff49) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 62), (3, 3), (4, 4), (5, 5), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff4e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 62), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff51) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 62), (2, 69), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff54) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 62), (2, 69), (3, 3), (4, 71), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120470) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l10ff24 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10ff24 :=
  Rest.liftedBlock (rest_l10ff24 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10ff24 x hx)

theorem rest_l10ff59 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10ff59 bytes_l10ff59) (entryMap (live .l10ff59))
      17 0x10ff59 bytes_l10ff59 b_l10ff59 := by
  have f0 : InstrSpec 0x10ff59 [0x48, 0x8B, 0x44, 0x24, 0x60] (LoadPre 0x10ff59 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10ff59 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff59 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10ff59 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x10ff59 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10ff5e [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x10ff5e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10ff5e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ff5e 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ff5e 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10ff5e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10ff63 [0x48, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x10ff63 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10ff63 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff63 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10ff63 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x10ff63 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10ff68 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x10ff68 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10ff68 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ff68 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ff68 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10ff68 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10ff6d [0x48, 0x8B, 0x44, 0x24, 0x70] (LoadPre 0x10ff6d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10ff6d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff6d 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10ff6d 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x10ff6d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10ff72 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x10ff72 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10ff72 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ff72 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ff72 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10ff72 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10ff77 [0x48, 0x8B, 0x44, 0x24, 0x78] (LoadPre 0x10ff77 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10ff77 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff77 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10ff77 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x10ff77 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10ff7c [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x10ff7c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10ff7c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ff7c 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ff7c 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10ff7c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10ff81 [0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x10ff81 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10ff81 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ff81 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10ff81 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x10ff81 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10ff89 [0x48, 0x89, 0x44, 0x24, 0x30] (StorePre 0x10ff89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10ff89 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ff89 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ff89 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10ff89 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10ff8e [0x4C, 0x8B, 0x6C, 0x24, 0x38] (LoadPre 0x10ff8e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10ff8e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff8e 13 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x10ff8e 13 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10ff8e 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10ff93 [0x48, 0x8B, 0x6C, 0x24, 0x40] (LoadPre 0x10ff93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10ff93 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff93 5 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x10ff93 5 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10ff93 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x10ff98 [0x4C, 0x8B, 0x74, 0x24, 0x48] (LoadPre 0x10ff98 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10ff98 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff98 14 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x10ff98 14 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10ff98 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10ff9d [0x4C, 0x8B, 0x7C, 0x24, 0x50] (LoadPre 0x10ff9d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10ff9d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff9d 15 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10ff9d 15 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x10ff9d 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10ffa2 [0x4C, 0x8B, 0x64, 0x24, 0x58] (LoadPre 0x10ffa2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10ffa2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ffa2 12 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x10ffa2 12 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x10ffa2 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x10ffa7 [0x8B, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x10ffa7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10ffa7 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x10ffa7 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x10ffa7 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r32_m32_low_effect_step 0x10ffa7 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10ffae [0xE8, 0x9D, 0x7D, 0x01, 0x00] (PushPre 0x10ffae 5) (callEffect (fun _ => 0x127d50) 0x10ffb3)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10ffae 0x127d50 0x10ffb3).toInstrSpec (call_rel32_effect_step 0x10ffae 0x17d9d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff5e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff63) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff68) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff6d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff72) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff77) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff7c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff81) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff89) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff8e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff93) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 70), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff98) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 70), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 68), (14, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff9d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 70), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 68), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffa2) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 70), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 68), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffa7) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 70), (6, 6), (7, 78), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 68), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffae) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 80), (5, 70), (6, 6), (7, 78), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 68), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f16 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 82) (by decide) (by decide) rfl rfl

theorem block_l10ff59 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10ff59 :=
  Rest.liftedBlock (rest_l10ff59 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10ff59 x hx)

theorem rest_l10ffb3_2 [Bindings] (code : CodeMap) :
    Rest (n := 117) code lifted (codeRange 0x10ffb3 bytes_l10ffb3) [(0, 114), (1, 111), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]
      9 0x110054 bytes_l10ffb3_2 b_l10ffb3_2 := by
  have f40 : InstrSpec 0x110054 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x110054) (movR64R64Effect 0x110054 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x110054 0 3).toInstrSpec (mov_r64_r64_effect_step 0x110054 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x110057 [0x48, 0x81, 0xC4, 0x48, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x110057) (addR64Imm32Effect 0x110057 4 0x148)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x110057 4 0x148).toInstrSpec (add_r64_imm32_effect_step 0x110057 0x48 0xc4 0x148 (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x11005e [0x5B] (PopPre 0x11005e) (popR64Effect 0x11005e 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11005e 1 3).toInstrSpec (pop_r64_effect_step 0x11005e 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f43 : InstrSpec 0x11005f [0x41, 0x5C] (PopPre 0x11005f) (popR64Effect 0x11005f 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11005f 2 12).toInstrSpec (pop_r64_rex_effect_step 0x11005f 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f44 : InstrSpec 0x110061 [0x41, 0x5D] (PopPre 0x110061) (popR64Effect 0x110061 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110061 2 13).toInstrSpec (pop_r64_rex_effect_step 0x110061 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f45 : InstrSpec 0x110063 [0x41, 0x5E] (PopPre 0x110063) (popR64Effect 0x110063 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110063 2 14).toInstrSpec (pop_r64_rex_effect_step 0x110063 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f46 : InstrSpec 0x110065 [0x41, 0x5F] (PopPre 0x110065) (popR64Effect 0x110065 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110065 2 15).toInstrSpec (pop_r64_rex_effect_step 0x110065 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f47 : InstrSpec 0x110067 [0x5D] (PopPre 0x110067) (popR64Effect 0x110067 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110067 1 5).toInstrSpec (pop_r64_effect_step 0x110067 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f48 : InstrSpec 0x110068 [0xC3] (RetPre 0x110068) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x110068).toInstrSpec (ret_effect_step 0x110068) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f40 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110057) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f41 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 3), (4, 119), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11005e) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f42 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 122) f42 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 123) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 121), (4, 122), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11005f) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f43 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 125) f43 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 126) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 121), (4, 125), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 124), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110061) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f44 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 128) f44 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 129) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 121), (4, 128), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 124), (13, 127), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110063) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f45 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 131) f45 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 132) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 121), (4, 131), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 124), (13, 127), (14, 130), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110065) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f46 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 134) f46 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 135) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 121), (4, 134), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 124), (13, 127), (14, 130), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110067) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f47 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 137) f47 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 138) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 121), (4, 137), (5, 136), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 124), (13, 127), (14, 130), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110068) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f48 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 140) f48 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 141) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 121), (4, 140), (5, 136), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 124), (13, 127), (14, 130), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) f48 (by decide) rfl rfl rfl (by decide)

theorem rest_l10ffb3_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x10ffb3 bytes_l10ffb3) [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]
      29 0x10fff8 bytes_l10ffb3_1 b_l10ffb3_1 := by
  have f20 : InstrSpec 0x10fff8 [0x48, 0x23, 0x44, 0x24, 0x30] (LoadPre 0x10fff8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10fff8 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x10fff8 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (andR64M64Effect_footprint 0x10fff8 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (and_r64_m64_effect_step 0x10fff8 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x10fffd [0x48, 0xC7, 0x43, 0x58, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10fffd 8 (fun s => AddrMode.addr (.base 3 (.d8 0x58)) s (0x10fffd + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10fffd (.base 3 (.d8 0x58)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10fffd (.base 3 (.d8 0x58)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10fffd 0x48 (by decide) (.base 3 (.d8 0x58)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x110005 [0x48, 0xC7, 0x43, 0x60, 0x00, 0x00, 0x00, 0x00] (StorePre 0x110005 8 (fun s => AddrMode.addr (.base 3 (.d8 0x60)) s (0x110005 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x110005 (.base 3 (.d8 0x60)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x110005 (.base 3 (.d8 0x60)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x110005 0x48 (by decide) (.base 3 (.d8 0x60)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x11000d [0x48, 0xC7, 0x43, 0x68, 0x00, 0x00, 0x00, 0x00] (StorePre 0x11000d 8 (fun s => AddrMode.addr (.base 3 (.d8 0x68)) s (0x11000d + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x11000d (.base 3 (.d8 0x68)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x11000d (.base 3 (.d8 0x68)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x11000d 0x48 (by decide) (.base 3 (.d8 0x68)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x110015 [0x48, 0xC7, 0x43, 0x70, 0x00, 0x00, 0x00, 0x00] (StorePre 0x110015 8 (fun s => AddrMode.addr (.base 3 (.d8 0x70)) s (0x110015 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x110015 (.base 3 (.d8 0x70)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x110015 (.base 3 (.d8 0x70)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x110015 0x48 (by decide) (.base 3 (.d8 0x70)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x11001d [0x4C, 0x89, 0x2B] (StorePre 0x11001d 3 (fun s => AddrMode.addr (.base 3 .none) s (0x11001d + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11001d 13 (.base 3 .none))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x11001d 13 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x11001d 0x4c (by decide) 5 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x110020 [0x48, 0x89, 0x6B, 0x08] (StorePre 0x110020 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x110020 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110020 5 (.base 3 (.d8 0x8)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x110020 5 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110020 0x48 (by decide) 5 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x110024 [0x4C, 0x89, 0x73, 0x10] (StorePre 0x110024 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x110024 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110024 14 (.base 3 (.d8 0x10)))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x110024 14 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x110024 0x4c (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x110028 [0x4C, 0x89, 0x7B, 0x18] (StorePre 0x110028 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x110028 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110028 15 (.base 3 (.d8 0x18)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x110028 15 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x110028 0x4c (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x11002c [0x4C, 0x89, 0x63, 0x20] (StorePre 0x11002c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x11002c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11002c 12 (.base 3 (.d8 0x20)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x11002c 12 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x11002c 0x4c (by decide) 4 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x110030 [0x48, 0x89, 0x53, 0x28] (StorePre 0x110030 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x110030 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110030 2 (.base 3 (.d8 0x28)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x110030 2 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x110030 0x48 (by decide) 2 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x110034 [0x48, 0x89, 0x73, 0x30] (StorePre 0x110034 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x110034 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110034 6 (.base 3 (.d8 0x30)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x110034 6 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x110034 0x48 (by decide) 6 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x110038 [0x48, 0x89, 0x7B, 0x38] (StorePre 0x110038 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x110038 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110038 7 (.base 3 (.d8 0x38)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x110038 7 (.base 3 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x110038 0x48 (by decide) 7 (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x11003c [0x4C, 0x89, 0x43, 0x40] (StorePre 0x11003c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x11003c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11003c 8 (.base 3 (.d8 0x40)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x11003c 8 (.base 3 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x11003c 0x4c (by decide) 0 (.base 3 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x110040 [0x48, 0x89, 0x43, 0x48] (StorePre 0x110040 4 (fun s => AddrMode.addr (.base 3 (.d8 0x48)) s (0x110040 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110040 0 (.base 3 (.d8 0x48)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x110040 0 (.base 3 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x110040 0x48 (by decide) 0 (.base 3 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x110044 [0xF7, 0xD1] (fun s => s.RIP = 0x110044) (notR32Effect 0x110044 2 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR32Effect_footprint 0x110044 2 1).toInstrSpec (not_r32_effect_step 0x110044 0xd1 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x110046 [0x83, 0xE1, 0x01] (fun s => s.RIP = 0x110046) (andR32Imm8Effect 0x110046 3 1 0x1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x110046 3 1 0x1).toInstrSpec (and_r32_imm8_effect_step 0x110046 0xe1 0x1 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x110049 [0x48, 0x89, 0x4B, 0x50] (StorePre 0x110049 4 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x110049 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110049 1 (.base 3 (.d8 0x50)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x110049 1 (.base 3 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x110049 0x48 (by decide) 1 (.base 3 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x11004d [0x8B, 0x44, 0x24, 0x0C] (LoadPre 0x11004d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x11004d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x11004d 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x11004d 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x11004d 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x110051 [0x88, 0x43, 0x78] (StorePre 0x110051 3 (fun s => AddrMode.addr (.base 3 (.d8 0x78)) s (0x110051 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110051 3 0 (.base 3 (.d8 0x78)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x110051 3 0 (.base 3 (.d8 0x78))).toInstrSpec (mov_m8_r8_effect_step 0x110051 0 (by decide) (.base 3 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fffd) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110005) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11000d) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110015) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11001d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110020) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110024) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110028) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.exec (n := 102) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11002c) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 103) (RestInside.exec (n := 103) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110030) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110034) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.exec (n := 105) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110038) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11003c) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110040) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 108) (RestInside.exec (n := 108) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110044) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f35 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 93), (1, 109), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110046) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f36 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 93), (1, 111), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110049) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.exec (n := 113) (ρ' := [(0, 93), (1, 111), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11004d) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f38 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 114), (1, 111), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110051) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.exec (n := 116) (ρ' := [(0, 114), (1, 111), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110054) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10ffb3_2 code

theorem rest_l10ffb3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10ffb3 bytes_l10ffb3) (entryMap (live .l10ffb3))
      49 0x10ffb3 bytes_l10ffb3 b_l10ffb3 := by
  have f0 : InstrSpec 0x10ffb3 [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x10ffb3) (movzxR32R8Effect 0x10ffb3 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x10ffb3 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x10ffb3 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10ffb6 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10ffb6) (movR64R64Effect 0x10ffb6 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10ffb6 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10ffb6 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10ffb9 [0x48, 0xF7, 0xD9] (fun s => s.RIP = 0x10ffb9) (negR64Effect 0x10ffb9 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR64Effect_footprint 0x10ffb9 1).toInstrSpec (neg_r64_effect_step 0x10ffb9 0x48 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10ffbc [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x10ffbc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10ffbc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ffbc 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10ffbc 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10ffbc 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10ffc1 [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x10ffc1) (movR64R64Effect 0x10ffc1 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10ffc1 2 6).toInstrSpec (mov_r64_r64_effect_step 0x10ffc1 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10ffc4 [0x48, 0x83, 0xF2, 0x01] (fun s => s.RIP = 0x10ffc4) (xorR64Imm8Effect 0x10ffc4 2 0x1)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR64Imm8Effect_footprint 0x10ffc4 2 0x1).toInstrSpec (xor_r64_imm8_effect_step 0x10ffc4 0x48 0xf2 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10ffc8 [0x48, 0x21, 0xCA] (fun s => s.RIP = 0x10ffc8) (andR64R64Effect 0x10ffc8 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ffc8 2 1).toInstrSpec (and_r64_r64_effect_step 0x10ffc8 0x48 0xca (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10ffcb [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x10ffcb) (xorR64R64Effect 0x10ffcb 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10ffcb 2 6).toInstrSpec (xor_r64_r64_effect_step 0x10ffcb 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10ffce [0x48, 0xFF, 0xC8] (fun s => s.RIP = 0x10ffce) (decR64Effect 0x10ffce 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (decR64Effect_footprint 0x10ffce 0).toInstrSpec (dec_r64_effect_step 0x10ffce 0x48 0xc8 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10ffd1 [0x49, 0x21, 0xC5] (fun s => s.RIP = 0x10ffd1) (andR64R64Effect 0x10ffd1 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ffd1 13 0).toInstrSpec (and_r64_r64_effect_step 0x10ffd1 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10ffd4 [0x48, 0x21, 0xC5] (fun s => s.RIP = 0x10ffd4) (andR64R64Effect 0x10ffd4 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ffd4 5 0).toInstrSpec (and_r64_r64_effect_step 0x10ffd4 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10ffd7 [0x49, 0x21, 0xC6] (fun s => s.RIP = 0x10ffd7) (andR64R64Effect 0x10ffd7 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ffd7 14 0).toInstrSpec (and_r64_r64_effect_step 0x10ffd7 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10ffda [0x49, 0x21, 0xC7] (fun s => s.RIP = 0x10ffda) (andR64R64Effect 0x10ffda 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ffda 15 0).toInstrSpec (and_r64_r64_effect_step 0x10ffda 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10ffdd [0x49, 0x21, 0xC4] (fun s => s.RIP = 0x10ffdd) (andR64R64Effect 0x10ffdd 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ffdd 12 0).toInstrSpec (and_r64_r64_effect_step 0x10ffdd 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10ffe0 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x10ffe0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10ffe0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ffe0 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10ffe0 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10ffe0 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x10ffe5 [0x48, 0x21, 0xC6] (fun s => s.RIP = 0x10ffe5) (andR64R64Effect 0x10ffe5 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ffe5 6 0).toInstrSpec (and_r64_r64_effect_step 0x10ffe5 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10ffe8 [0x48, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x10ffe8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10ffe8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ffe8 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10ffe8 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10ffe8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10ffed [0x48, 0x21, 0xC7] (fun s => s.RIP = 0x10ffed) (andR64R64Effect 0x10ffed 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ffed 7 0).toInstrSpec (and_r64_r64_effect_step 0x10ffed 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10fff0 [0x4C, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x10fff0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10fff0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10fff0 8 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10fff0 8 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10fff0 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x10fff5 [0x49, 0x21, 0xC0] (fun s => s.RIP = 0x10fff5) (andR64R64Effect 0x10fff5 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fff5 8 0).toInstrSpec (and_r64_r64_effect_step 0x10fff5 0x49 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffb6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffb9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffbc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffc1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 57), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffc4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 57), (2, 63), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffc8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 57), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffcb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 57), (2, 67), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffce) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffd1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffd4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffd7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffda) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffdd) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffe0) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 81), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffe5) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffe8) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 85), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffed) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fff0) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 89), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fff5) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fff8) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10ffb3_1 code

theorem block_l10ffb3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10ffb3 :=
  Rest.liftedBlock (rest_l10ffb3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10ffb3 x hx)

theorem rest_l110070 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110070 bytes_l110070) (entryMap (live .l110070))
      7 0x110070 bytes_l110070 b_l110070 := by
  have f0 : InstrSpec 0x110070 [0x41, 0x56] (PushPre 0x110070 2) (pushR64Effect 0x110070 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x110070 2 14).toInstrSpec (push_r64_rex_effect_step 0x110070 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x110072 [0x53] (PushPre 0x110072 1) (pushR64Effect 0x110072 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x110072 1 3).toInstrSpec (push_r64_effect_step 0x110072 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x110073 [0x48, 0x83, 0xEC, 0x58] (fun s => s.RIP = 0x110073) (subR64Imm8Effect 0x110073 4 0x58)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x110073 4 0x58).toInstrSpec (sub_r64_imm8_effect_step 0x110073 0x48 0xec 0x58 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x110077 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x110077) (movR64R64Effect 0x110077 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x110077 3 7).toInstrSpec (mov_r64_r64_effect_step 0x110077 0x48 0xfb (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11007a [0x49, 0x89, 0xE6] (fun s => s.RIP = 0x11007a) (movR64R64Effect 0x11007a 14 4)
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x11007a 14 4).toInstrSpec (mov_r64_r64_effect_step 0x11007a 0x49 0xe6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11007d [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11007d) (movR64R64Effect 0x11007d 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11007d 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11007d 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x110080 [0xE8, 0x5B, 0xEC, 0xFF, 0xFF] (PushPre 0x110080 5) (callEffect (fun _ => 0x10ece0) 0x110085)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x110080 0x10ece0 0x110085).toInstrSpec (call_rel32_effect_step 0x110080 0xffffec5b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110072) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110073) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110077) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11007a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11007d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 59), (4, 57), (5, 5), (6, 6), (7, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110080) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 59), (4, 65), (5, 5), (6, 6), (7, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ece0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l110070 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110070 :=
  Rest.liftedBlock (rest_l110070 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110070 x hx)

theorem rest_l110085 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110085 bytes_l110085) (entryMap (live .l110085))
      3 0x110085 bytes_l110085 b_l110085 := by
  have f0 : InstrSpec 0x110085 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x110085) (movR64R64Effect 0x110085 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x110085 7 3).toInstrSpec (mov_r64_r64_effect_step 0x110085 0x48 0xdf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110088 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x110088) (movR64R64Effect 0x110088 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x110088 6 14).toInstrSpec (mov_r64_r64_effect_step 0x110088 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11008b [0xE8, 0x20, 0x11, 0x01, 0x00] (PushPre 0x11008b 5) (callEffect (fun _ => 0x1211b0) 0x110090)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11008b 0x1211b0 0x110090).toInstrSpec (call_rel32_effect_step 0x11008b 0x11120 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110088) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11008b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211b0) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l110085 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110085 :=
  Rest.liftedBlock (rest_l110085 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110085 x hx)

theorem rest_l110090 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110090 bytes_l110090) (entryMap (live .l110090))
      5 0x110090 bytes_l110090 b_l110090 := by
  have f0 : InstrSpec 0x110090 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x110090) (movR64R64Effect 0x110090 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x110090 0 3).toInstrSpec (mov_r64_r64_effect_step 0x110090 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110093 [0x48, 0x83, 0xC4, 0x58] (fun s => s.RIP = 0x110093) (addR64Imm8Effect 0x110093 4 0x58)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x110093 4 0x58).toInstrSpec (add_r64_imm8_effect_step 0x110093 0x48 0xc4 0x58 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x110097 [0x5B] (PopPre 0x110097) (popR64Effect 0x110097 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110097 1 3).toInstrSpec (pop_r64_effect_step 0x110097 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x110098 [0x41, 0x5E] (PopPre 0x110098) (popR64Effect 0x110098 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110098 2 14).toInstrSpec (pop_r64_rex_effect_step 0x110098 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x11009a [0xC3] (RetPre 0x11009a) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x11009a).toInstrSpec (ret_effect_step 0x11009a) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110093) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110097) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110098) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11009a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l110090 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110090 :=
  Rest.liftedBlock (rest_l110090 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110090 x hx)

theorem rest_l110b80_4 [Bindings] (code : CodeMap) :
    Rest (n := 204) code lifted (codeRange 0x110b80 bytes_l110b80) [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]
      17 0x110c99 bytes_l110b80_4 b_l110b80_4 := by
  have f80 : InstrSpec 0x110c99 [0x49, 0xFF, 0xCA] (fun s => s.RIP = 0x110c99) (decR64Effect 0x110c99 10)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (decR64Effect_footprint 0x110c99 10).toInstrSpec (dec_r64_effect_step 0x110c99 0x49 0xca (by decide) (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x110c9c [0x4D, 0x21, 0xC2] (fun s => s.RIP = 0x110c9c) (andR64R64Effect 0x110c9c 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c9c 10 8).toInstrSpec (and_r64_r64_effect_step 0x110c9c 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x110c9f [0x49, 0xFF, 0xCB] (fun s => s.RIP = 0x110c9f) (decR64Effect 0x110c9f 11)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (decR64Effect_footprint 0x110c9f 11).toInstrSpec (dec_r64_effect_step 0x110c9f 0x49 0xcb (by decide) (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x110ca2 [0x49, 0x21, 0xDB] (fun s => s.RIP = 0x110ca2) (andR64R64Effect 0x110ca2 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110ca2 11 3).toInstrSpec (and_r64_r64_effect_step 0x110ca2 0x49 0xdb (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x110ca5 [0x0F, 0xB6, 0x4C, 0x24, 0x07] (LoadPre 0x110ca5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110ca5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x110ca5 5 1 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x110ca5 5 1 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x110ca5 1 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f85 : InstrSpec 0x110caa [0x48, 0xFF, 0xC9] (fun s => s.RIP = 0x110caa) (decR64Effect 0x110caa 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (decR64Effect_footprint 0x110caa 1).toInstrSpec (dec_r64_effect_step 0x110caa 0x48 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x110cad [0x48, 0x21, 0xF1] (fun s => s.RIP = 0x110cad) (andR64R64Effect 0x110cad 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110cad 1 6).toInstrSpec (and_r64_r64_effect_step 0x110cad 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x110cb0 [0x48, 0x89, 0x17] (StorePre 0x110cb0 3 (fun s => AddrMode.addr (.base 7 .none) s (0x110cb0 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x110cb0 2 (.base 7 .none))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x110cb0 2 (.base 7 .none)).toInstrSpec (mov_m64_r64_effect_step 0x110cb0 0x48 (by decide) 2 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f88 : InstrSpec 0x110cb3 [0x4C, 0x89, 0x57, 0x08] (StorePre 0x110cb3 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x110cb3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110cb3 10 (.base 7 (.d8 0x8)))
      [.gpr 10, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x110cb3 10 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110cb3 0x4c (by decide) 2 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f89 : InstrSpec 0x110cb7 [0x4C, 0x89, 0x5F, 0x10] (StorePre 0x110cb7 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x110cb7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110cb7 11 (.base 7 (.d8 0x10)))
      [.gpr 11, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x110cb7 11 (.base 7 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x110cb7 0x4c (by decide) 3 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f90 : InstrSpec 0x110cbb [0x48, 0x89, 0x4F, 0x18] (StorePre 0x110cbb 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x110cbb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110cbb 1 (.base 7 (.d8 0x18)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x110cbb 1 (.base 7 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x110cbb 0x48 (by decide) 1 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f91 : InstrSpec 0x110cbf [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x110cbf) (addR64Imm8Effect 0x110cbf 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x110cbf 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x110cbf 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x110cc3 [0x5B] (PopPre 0x110cc3) (popR64Effect 0x110cc3 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110cc3 1 3).toInstrSpec (pop_r64_effect_step 0x110cc3 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f93 : InstrSpec 0x110cc4 [0x41, 0x5C] (PopPre 0x110cc4) (popR64Effect 0x110cc4 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110cc4 2 12).toInstrSpec (pop_r64_rex_effect_step 0x110cc4 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f94 : InstrSpec 0x110cc6 [0x41, 0x5E] (PopPre 0x110cc6) (popR64Effect 0x110cc6 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110cc6 2 14).toInstrSpec (pop_r64_rex_effect_step 0x110cc6 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f95 : InstrSpec 0x110cc8 [0x41, 0x5F] (PopPre 0x110cc8) (popR64Effect 0x110cc8 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110cc8 2 15).toInstrSpec (pop_r64_rex_effect_step 0x110cc8 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f96 : InstrSpec 0x110cca [0xC3] (RetPre 0x110cca) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x110cca).toInstrSpec (ret_effect_step 0x110cca) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f80 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 204), (11, 195), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c9c) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f81 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 195), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c9f) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f82 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 208), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ca2) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f83 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ca5) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f84 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 198), (1, 212), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110caa) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f85 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 198), (1, 214), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cad) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f86 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cb0) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 218) (RestInside.exec (n := 218) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cb3) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 219) (RestInside.exec (n := 219) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cb7) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 220) (RestInside.exec (n := 220) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cbb) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 221) (RestInside.exec (n := 221) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cbf) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 222) (RestInside.out (n := 222) f91 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 223) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 222), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cc3) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 224) (RestInside.out (n := 224) f92 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 225) f92 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 226) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 224), (4, 225), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cc4) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f93 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 228) f93 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 229) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 224), (4, 228), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 227), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cc6) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 230) (RestInside.out (n := 230) f94 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 231) f94 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 232) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 224), (4, 231), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 227), (13, 13), (14, 230), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cc8) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 233) (RestInside.out (n := 233) f95 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 234) f95 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 235) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 224), (4, 234), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 227), (13, 13), (14, 230), (15, 233), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cca) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f96 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 237) f96 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 238) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 224), (4, 237), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 227), (13, 13), (14, 230), (15, 233), (22, 22), (39, 39), (50, 50), (51, 51)]) f96 (by decide) rfl rfl rfl (by decide)

theorem rest_l110b80_3 [Bindings] (code : CodeMap) :
    Rest (n := 169) code lifted (codeRange 0x110b80 bytes_l110b80) [(0, 65), (1, 75), (2, 165), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 167), (22, 22), (39, 39), (50, 50), (51, 51)]
      37 0x110c48 bytes_l110b80_3 b_l110b80_3 := by
  have f60 : InstrSpec 0x110c48 [0x49, 0x21, 0xD7] (fun s => s.RIP = 0x110c48) (andR64R64Effect 0x110c48 15 2)
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c48 15 2).toInstrSpec (and_r64_r64_effect_step 0x110c48 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x110c4b [0x4C, 0x09, 0xCA] (fun s => s.RIP = 0x110c4b) (orR64R64Effect 0x110c4b 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c4b 2 9).toInstrSpec (or_r64_r64_effect_step 0x110c4b 0x4c 0xca (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x110c4e [0x48, 0x21, 0xF2] (fun s => s.RIP = 0x110c4e) (andR64R64Effect 0x110c4e 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c4e 2 6).toInstrSpec (and_r64_r64_effect_step 0x110c4e 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x110c51 [0x4C, 0x09, 0xFA] (fun s => s.RIP = 0x110c51) (orR64R64Effect 0x110c51 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c51 2 15).toInstrSpec (or_r64_r64_effect_step 0x110c51 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x110c54 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x110c54) (shrR64Effect 0x110c54 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x110c54 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x110c54 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x110c58 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x110c58 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110c58 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110c58 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110c58 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110c58 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f66 : InstrSpec 0x110c5d [0x4C, 0x09, 0xD0] (fun s => s.RIP = 0x110c5d) (orR64R64Effect 0x110c5d 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c5d 0 10).toInstrSpec (or_r64_r64_effect_step 0x110c5d 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x110c60 [0x4C, 0x09, 0xD8] (fun s => s.RIP = 0x110c60) (orR64R64Effect 0x110c60 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c60 0 11).toInstrSpec (or_r64_r64_effect_step 0x110c60 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x110c63 [0x4C, 0x09, 0xC8] (fun s => s.RIP = 0x110c63) (orR64R64Effect 0x110c63 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c63 0 9).toInstrSpec (or_r64_r64_effect_step 0x110c63 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x110c66 [0x0F, 0x94, 0x44, 0x24, 0x07] (StorePre 0x110c66 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c66 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c66 5 (.sib 4 none 0 (.d8 0x7))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x110c66 5 (.sib 4 none 0 (.d8 0x7)) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x110c66 4 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f70 : InstrSpec 0x110c6b [0x4C, 0x8D, 0x4C, 0x24, 0x07] (fun s => s.RIP = 0x110c6b) (leaR64Effect 0x110c6b 9 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x110c6b 9 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x110c6b 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x110c70 [0x0F, 0xB6, 0x54, 0x24, 0x07] (LoadPre 0x110c70 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c70 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x110c70 5 2 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x110c70 5 2 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x110c70 2 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f72 : InstrSpec 0x110c75 [0x0F, 0x94, 0x44, 0x24, 0x07] (StorePre 0x110c75 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c75 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c75 5 (.sib 4 none 0 (.d8 0x7))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x110c75 5 (.sib 4 none 0 (.d8 0x7)) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x110c75 4 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f73 : InstrSpec 0x110c7a [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x07] (LoadPre 0x110c7a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c7a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x110c7a 6 10 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x110c7a 6 10 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x110c7a 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f74 : InstrSpec 0x110c80 [0x0F, 0x94, 0x44, 0x24, 0x07] (StorePre 0x110c80 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c80 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c80 5 (.sib 4 none 0 (.d8 0x7))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x110c80 5 (.sib 4 none 0 (.d8 0x7)) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x110c80 4 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f75 : InstrSpec 0x110c85 [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x07] (LoadPre 0x110c85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c85 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x110c85 6 11 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x110c85 6 11 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x110c85 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f76 : InstrSpec 0x110c8b [0x0F, 0x94, 0x44, 0x24, 0x07] (StorePre 0x110c8b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c8b + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c8b 5 (.sib 4 none 0 (.d8 0x7))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x110c8b 5 (.sib 4 none 0 (.d8 0x7)) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x110c8b 4 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f77 : InstrSpec 0x110c90 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x110c90) (movR64R64Effect 0x110c90 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x110c90 0 7).toInstrSpec (mov_r64_r64_effect_step 0x110c90 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x110c93 [0x48, 0xFF, 0xCA] (fun s => s.RIP = 0x110c93) (decR64Effect 0x110c93 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (decR64Effect_footprint 0x110c93 2).toInstrSpec (dec_r64_effect_step 0x110c93 0x48 0xca (by decide) (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x110c96 [0x48, 0x21, 0xCA] (fun s => s.RIP = 0x110c96) (andR64R64Effect 0x110c96 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c96 2 1).toInstrSpec (and_r64_r64_effect_step 0x110c96 0x48 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f60 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 65), (1, 75), (2, 165), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c4b) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f61 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 65), (1, 75), (2, 171), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c4e) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f62 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 65), (1, 75), (2, 173), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c51) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f63 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 65), (1, 75), (2, 175), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c54) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f64 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 65), (1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c58) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.exec (n := 179) (ρ' := [(0, 65), (1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c5d) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f66 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(0, 180), (1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c60) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f67 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 182), (1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c63) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f68 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c66) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 186) (RestInside.exec (n := 186) (ρ' := [(1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c6b) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f70 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c70) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f71 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c75) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.exec (n := 191) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c7a) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 192) (RestInside.out (n := 192) f73 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 193) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c80) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 194) (RestInside.exec (n := 194) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c85) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f75 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c8b) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.exec (n := 197) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c90) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 198) (RestInside.out (n := 198) f77 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 199) (ρ' := [(0, 198), (1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c93) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f78 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 198), (1, 75), (2, 200), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c96) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f79 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c99) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l110b80_4 code

theorem rest_l110b80_2 [Bindings] (code : CodeMap) :
    Rest (n := 130) code lifted (codeRange 0x110b80 bytes_l110b80) [(0, 65), (1, 75), (2, 2), (3, 126), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]
      57 0x110c04 bytes_l110b80_2 b_l110b80_2 := by
  have f40 : InstrSpec 0x110c04 [0x4D, 0x89, 0xFC] (fun s => s.RIP = 0x110c04) (movR64R64Effect 0x110c04 12 15)
      [.gpr 15] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x110c04 12 15).toInstrSpec (mov_r64_r64_effect_step 0x110c04 0x4d 0xfc (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x110c07 [0x4D, 0x29, 0xDC] (fun s => s.RIP = 0x110c07) (subR64R64Effect 0x110c07 12 11)
      [.gpr 12, .gpr 11] [] [.reg 12, .flags, .rip] :=
    (subR64R64Effect_footprint 0x110c07 12 11).toInstrSpec (sub_r64_r64_effect_step 0x110c07 0x4d 0xdc (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x110c0a [0x48, 0xC1, 0xFB, 0x3F] (fun s => s.RIP = 0x110c0a) (sarR64Effect 0x110c0a 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (sarR64Effect_footprint 0x110c0a 4 3 63).toInstrSpec (sar_r64_imm8_effect_step 0x110c0a 0x48 0xfb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x110c0e [0x4C, 0x01, 0xE3] (fun s => s.RIP = 0x110c0e) (addR64R64Effect 0x110c0e 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x110c0e 3 12).toInstrSpec (add_r64_r64_effect_step 0x110c0e 0x4c 0xe3 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x110c11 [0x49, 0xF7, 0xD7] (fun s => s.RIP = 0x110c11) (notR64Effect 0x110c11 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (notR64Effect_footprint 0x110c11 15).toInstrSpec (not_r64_effect_step 0x110c11 0x49 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x110c14 [0x4D, 0x89, 0xDC] (fun s => s.RIP = 0x110c14) (movR64R64Effect 0x110c14 12 11)
      [.gpr 11] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x110c14 12 11).toInstrSpec (mov_r64_r64_effect_step 0x110c14 0x4d 0xdc (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x110c17 [0x4D, 0x21, 0xFC] (fun s => s.RIP = 0x110c17) (andR64R64Effect 0x110c17 12 15)
      [.gpr 12, .gpr 15] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c17 12 15).toInstrSpec (and_r64_r64_effect_step 0x110c17 0x4d 0xfc (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x110c1a [0x4D, 0x09, 0xDF] (fun s => s.RIP = 0x110c1a) (orR64R64Effect 0x110c1a 15 11)
      [.gpr 15, .gpr 11] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c1a 15 11).toInstrSpec (or_r64_r64_effect_step 0x110c1a 0x4d 0xdf (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x110c1d [0x49, 0x21, 0xDF] (fun s => s.RIP = 0x110c1d) (andR64R64Effect 0x110c1d 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c1d 15 3).toInstrSpec (and_r64_r64_effect_step 0x110c1d 0x49 0xdf (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x110c20 [0x4D, 0x09, 0xE7] (fun s => s.RIP = 0x110c20) (orR64R64Effect 0x110c20 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c20 15 12).toInstrSpec (or_r64_r64_effect_step 0x110c20 0x4d 0xe7 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x110c23 [0x49, 0xC1, 0xEF, 0x3F] (fun s => s.RIP = 0x110c23) (shrR64Effect 0x110c23 4 15 63)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x110c23 4 15 63).toInstrSpec (shr_r64_imm8_effect_step 0x110c23 0x49 0xef 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x110c27 [0x4C, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x110c27 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110c27 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110c27 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110c27 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110c27 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x110c2c [0x48, 0x2B, 0x74, 0x24, 0x08] (LoadPre 0x110c2c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110c2c + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110c2c 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (subR64M64Effect_footprint 0x110c2c 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x110c2c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f53 : InstrSpec 0x110c31 [0x48, 0x8B, 0x52, 0x18] (LoadPre 0x110c31 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x110c31 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110c31 2 (.base 2 (.d8 0x18)))
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x110c31 2 (.base 2 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x110c31 0x48 (by decide) 2 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f54 : InstrSpec 0x110c35 [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x110c35) (movR64R64Effect 0x110c35 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x110c35 15 2).toInstrSpec (mov_r64_r64_effect_step 0x110c35 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x110c38 [0x4D, 0x29, 0xCF] (fun s => s.RIP = 0x110c38) (subR64R64Effect 0x110c38 15 9)
      [.gpr 15, .gpr 9] [] [.reg 15, .flags, .rip] :=
    (subR64R64Effect_footprint 0x110c38 15 9).toInstrSpec (sub_r64_r64_effect_step 0x110c38 0x4d 0xcf (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x110c3b [0x48, 0xC1, 0xFE, 0x3F] (fun s => s.RIP = 0x110c3b) (sarR64Effect 0x110c3b 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (sarR64Effect_footprint 0x110c3b 4 6 63).toInstrSpec (sar_r64_imm8_effect_step 0x110c3b 0x48 0xfe 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x110c3f [0x4C, 0x01, 0xFE] (fun s => s.RIP = 0x110c3f) (addR64R64Effect 0x110c3f 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x110c3f 6 15).toInstrSpec (add_r64_r64_effect_step 0x110c3f 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x110c42 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x110c42) (notR64Effect 0x110c42 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x110c42 2).toInstrSpec (not_r64_effect_step 0x110c42 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x110c45 [0x4D, 0x89, 0xCF] (fun s => s.RIP = 0x110c45) (movR64R64Effect 0x110c45 15 9)
      [.gpr 9] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x110c45 15 9).toInstrSpec (mov_r64_r64_effect_step 0x110c45 0x4d 0xcf (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f40 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 126), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 130), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c07) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f41 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 126), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 132), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c0a) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f42 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 134), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 132), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c0e) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f43 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 132), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c11) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f44 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 132), (13, 13), (15, 138), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c14) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f45 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 140), (13, 13), (15, 138), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c17) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f46 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 138), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c1a) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f47 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 144), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c1d) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f48 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c20) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f49 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c23) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f50 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 150), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c27) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.exec (n := 152) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 150), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c2c) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f52 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 153), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 150), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c31) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f53 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 65), (1, 75), (2, 155), (3, 136), (4, 61), (5, 5), (6, 153), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 150), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c35) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f54 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 65), (1, 75), (2, 155), (3, 136), (4, 61), (5, 5), (6, 153), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c38) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f55 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 65), (1, 75), (2, 155), (3, 136), (4, 61), (5, 5), (6, 153), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 159), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c3b) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f56 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 65), (1, 75), (2, 155), (3, 136), (4, 61), (5, 5), (6, 161), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 159), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c3f) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f57 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 65), (1, 75), (2, 155), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 159), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c42) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f58 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 65), (1, 75), (2, 165), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 159), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c45) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f59 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 65), (1, 75), (2, 165), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 167), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c48) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l110b80_3 code

theorem rest_l110b80_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x110b80 bytes_l110b80) [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 89), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      77 0x110bbe bytes_l110b80_1 b_l110b80_1 := by
  have f20 : InstrSpec 0x110bbe [0x4C, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x110bbe) (leaR64Effect 0x110bbe 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x110bbe 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x110bbe 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x110bc3 [0x31, 0xF6] (fun s => s.RIP = 0x110bc3) (xorR32R32Effect 0x110bc3 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x110bc3 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x110bc3 0xf6 (by decide)) pre_rip
  have f22 : InstrSpec 0x110bc5 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x110bc5) (xorR32R32Effect 0x110bc5 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x110bc5 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x110bc5 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x110bc8 [0x4C, 0x2B, 0x44, 0x24, 0x08] (LoadPre 0x110bc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bc8 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110bc8 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 8, .gpr 4] [] [.reg 8, .flags, .rip] :=
    (subR64M64Effect_footprint 0x110bc8 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x110bc8 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x110bcd [0x48, 0x8B, 0x5A, 0x08] (LoadPre 0x110bcd (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x110bcd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110bcd 3 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x110bcd 3 (.base 2 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x110bcd 0x48 (by decide) 3 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x110bd1 [0x49, 0x89, 0xDF] (fun s => s.RIP = 0x110bd1) (movR64R64Effect 0x110bd1 15 3)
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x110bd1 15 3).toInstrSpec (mov_r64_r64_effect_step 0x110bd1 0x49 0xdf (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x110bd4 [0x49, 0x29, 0xC7] (fun s => s.RIP = 0x110bd4) (subR64R64Effect 0x110bd4 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (subR64R64Effect_footprint 0x110bd4 15 0).toInstrSpec (sub_r64_r64_effect_step 0x110bd4 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x110bd7 [0x49, 0xC1, 0xF8, 0x3F] (fun s => s.RIP = 0x110bd7) (sarR64Effect 0x110bd7 4 8 63)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (sarR64Effect_footprint 0x110bd7 4 8 63).toInstrSpec (sar_r64_imm8_effect_step 0x110bd7 0x49 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x110bdb [0x4D, 0x01, 0xF8] (fun s => s.RIP = 0x110bdb) (addR64R64Effect 0x110bdb 8 15)
      [.gpr 8, .gpr 15] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x110bdb 8 15).toInstrSpec (add_r64_r64_effect_step 0x110bdb 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x110bde [0x48, 0xF7, 0xD3] (fun s => s.RIP = 0x110bde) (notR64Effect 0x110bde 3)
      [.gpr 3] [] [.reg 3, .rip] :=
    (notR64Effect_footprint 0x110bde 3).toInstrSpec (not_r64_effect_step 0x110bde 0x48 0xd3 (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x110be1 [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x110be1) (movR64R64Effect 0x110be1 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x110be1 15 0).toInstrSpec (mov_r64_r64_effect_step 0x110be1 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x110be4 [0x49, 0x21, 0xDF] (fun s => s.RIP = 0x110be4) (andR64R64Effect 0x110be4 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110be4 15 3).toInstrSpec (and_r64_r64_effect_step 0x110be4 0x49 0xdf (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x110be7 [0x48, 0x09, 0xC3] (fun s => s.RIP = 0x110be7) (orR64R64Effect 0x110be7 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110be7 3 0).toInstrSpec (or_r64_r64_effect_step 0x110be7 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x110bea [0x4C, 0x21, 0xC3] (fun s => s.RIP = 0x110bea) (andR64R64Effect 0x110bea 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110bea 3 8).toInstrSpec (and_r64_r64_effect_step 0x110bea 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x110bed [0x4C, 0x09, 0xFB] (fun s => s.RIP = 0x110bed) (orR64R64Effect 0x110bed 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110bed 3 15).toInstrSpec (or_r64_r64_effect_step 0x110bed 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x110bf0 [0x48, 0xC1, 0xEB, 0x3F] (fun s => s.RIP = 0x110bf0) (shrR64Effect 0x110bf0 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x110bf0 4 3 63).toInstrSpec (shr_r64_imm8_effect_step 0x110bf0 0x48 0xeb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x110bf4 [0x48, 0x89, 0x5C, 0x24, 0x08] (StorePre 0x110bf4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bf4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110bf4 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110bf4 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110bf4 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x110bf9 [0x31, 0xDB] (fun s => s.RIP = 0x110bf9) (xorR32R32Effect 0x110bf9 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x110bf9 2 3 3).toInstrSpec (xor_r32_r32_effect_step 0x110bf9 0xdb (by decide)) pre_rip
  have f38 : InstrSpec 0x110bfb [0x48, 0x2B, 0x5C, 0x24, 0x08] (LoadPre 0x110bfb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bfb + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110bfb 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.reg 3, .flags, .rip] :=
    (subR64M64Effect_footprint 0x110bfb 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x110bfb 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x110c00 [0x4C, 0x8B, 0x7A, 0x10] (LoadPre 0x110c00 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x110c00 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110c00 15 (.base 2 (.d8 0x10)))
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x110c00 15 (.base 2 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x110c00 0x4c (by decide) 7 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 89), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bc3) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 93), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bc5) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 93), (7, 7), (8, 95), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bc8) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 93), (7, 7), (8, 97), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bcd) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 99), (4, 61), (5, 5), (6, 93), (7, 7), (8, 97), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bd1) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f25 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 99), (4, 61), (5, 5), (6, 93), (7, 7), (8, 97), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bd4) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 99), (4, 61), (5, 5), (6, 93), (7, 7), (8, 97), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bd7) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 99), (4, 61), (5, 5), (6, 93), (7, 7), (8, 105), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bdb) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f28 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 99), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bde) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f29 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 109), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110be1) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f30 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 109), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110be4) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f31 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 109), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110be7) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f32 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 115), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bea) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f33 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 117), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bed) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f34 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 119), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bf0) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f35 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 121), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bf4) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.exec (n := 123) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 121), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bf9) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f37 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 124), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bfb) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f38 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 126), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c00) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f39 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 126), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c04) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l110b80_2 code

theorem rest_l110b80 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110b80 bytes_l110b80) (entryMap (live .l110b80))
      97 0x110b80 bytes_l110b80 b_l110b80 := by
  have f0 : InstrSpec 0x110b80 [0x41, 0x57] (PushPre 0x110b80 2) (pushR64Effect 0x110b80 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x110b80 2 15).toInstrSpec (push_r64_rex_effect_step 0x110b80 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x110b82 [0x41, 0x56] (PushPre 0x110b82 2) (pushR64Effect 0x110b82 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x110b82 2 14).toInstrSpec (push_r64_rex_effect_step 0x110b82 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x110b84 [0x41, 0x54] (PushPre 0x110b84 2) (pushR64Effect 0x110b84 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x110b84 2 12).toInstrSpec (push_r64_rex_effect_step 0x110b84 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x110b86 [0x53] (PushPre 0x110b86 1) (pushR64Effect 0x110b86 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x110b86 1 3).toInstrSpec (push_r64_effect_step 0x110b86 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x110b87 [0x48, 0x83, 0xEC, 0x10] (fun s => s.RIP = 0x110b87) (subR64Imm8Effect 0x110b87 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x110b87 4 0x10).toInstrSpec (sub_r64_imm8_effect_step 0x110b87 0x48 0xec 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x110b8b [0x4C, 0x8B, 0x16] (LoadPre 0x110b8b (fun s => AddrMode.addr (.base 6 .none) s (0x110b8b + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x110b8b 10 (.base 6 .none))
      [.gpr 6] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x110b8b 10 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x110b8b 0x4c (by decide) 2 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x110b8e [0x48, 0x8B, 0x46, 0x08] (LoadPre 0x110b8e (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x110b8e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110b8e 0 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x110b8e 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x110b8e 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x110b92 [0x4C, 0x8B, 0x5E, 0x10] (LoadPre 0x110b92 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x110b92 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110b92 11 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x110b92 11 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x110b92 0x4c (by decide) 3 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x110b96 [0x4C, 0x8B, 0x4E, 0x18] (LoadPre 0x110b96 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x110b96 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110b96 9 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x110b96 9 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x110b96 0x4c (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x110b9a [0x48, 0x8B, 0x32] (LoadPre 0x110b9a (fun s => AddrMode.addr (.base 2 .none) s (0x110b9a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x110b9a 6 (.base 2 .none))
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x110b9a 6 (.base 2 .none)).toInstrSpec (mov_r64_m64_effect_step 0x110b9a 0x48 (by decide) 6 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x110b9d [0x48, 0x89, 0xF1] (fun s => s.RIP = 0x110b9d) (movR64R64Effect 0x110b9d 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x110b9d 1 6).toInstrSpec (mov_r64_r64_effect_step 0x110b9d 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x110ba0 [0x4C, 0x29, 0xD1] (fun s => s.RIP = 0x110ba0) (subR64R64Effect 0x110ba0 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x110ba0 1 10).toInstrSpec (sub_r64_r64_effect_step 0x110ba0 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x110ba3 [0x48, 0xF7, 0xD6] (fun s => s.RIP = 0x110ba3) (notR64Effect 0x110ba3 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR64Effect_footprint 0x110ba3 6).toInstrSpec (not_r64_effect_step 0x110ba3 0x48 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x110ba6 [0x4D, 0x89, 0xD0] (fun s => s.RIP = 0x110ba6) (movR64R64Effect 0x110ba6 8 10)
      [.gpr 10] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x110ba6 8 10).toInstrSpec (mov_r64_r64_effect_step 0x110ba6 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x110ba9 [0x49, 0x21, 0xF0] (fun s => s.RIP = 0x110ba9) (andR64R64Effect 0x110ba9 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110ba9 8 6).toInstrSpec (and_r64_r64_effect_step 0x110ba9 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x110bac [0x4C, 0x09, 0xD6] (fun s => s.RIP = 0x110bac) (orR64R64Effect 0x110bac 6 10)
      [.gpr 6, .gpr 10] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110bac 6 10).toInstrSpec (or_r64_r64_effect_step 0x110bac 0x4c 0xd6 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x110baf [0x48, 0x21, 0xCE] (fun s => s.RIP = 0x110baf) (andR64R64Effect 0x110baf 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110baf 6 1).toInstrSpec (and_r64_r64_effect_step 0x110baf 0x48 0xce (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x110bb2 [0x4C, 0x09, 0xC6] (fun s => s.RIP = 0x110bb2) (orR64R64Effect 0x110bb2 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110bb2 6 8).toInstrSpec (or_r64_r64_effect_step 0x110bb2 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x110bb5 [0x48, 0xC1, 0xEE, 0x3F] (fun s => s.RIP = 0x110bb5) (shrR64Effect 0x110bb5 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x110bb5 4 6 63).toInstrSpec (shr_r64_imm8_effect_step 0x110bb5 0x48 0xee 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x110bb9 [0x48, 0x89, 0x74, 0x24, 0x08] (StorePre 0x110bb9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bb9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110bb9 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110bb9 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110bb9 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b82) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b84) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b86) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b87) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b8b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (10, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b8e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (10, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b92) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b96) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b9a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 65), (2, 2), (3, 3), (4, 61), (5, 5), (6, 71), (7, 7), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b9d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 65), (1, 73), (2, 2), (3, 3), (4, 61), (5, 5), (6, 71), (7, 7), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ba0) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 71), (7, 7), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ba3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 77), (7, 7), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ba6) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 77), (7, 7), (8, 79), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ba9) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 77), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bac) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 83), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110baf) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 85), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bb2) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 87), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bb5) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 89), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bb9) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 89), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bbe) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l110b80_1 code

theorem block_l110b80 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110b80 :=
  Rest.liftedBlock (rest_l110b80 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110b80 x hx)

theorem rest_l1148d0_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x1148d0 bytes_l1148d0) [(0, 67), (1, 65), (2, 89), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      8 0x114917 bytes_l1148d0_1 b_l1148d0_1 := by
  have f20 : InstrSpec 0x114917 [0x48, 0x0F, 0xCE] (fun s => s.RIP = 0x114917) (bswapR64Effect 0x114917 3 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (bswapR64Effect_footprint 0x114917 3 6).toInstrSpec (bswap_r64_effect_step 0x114917 0x48 (by decide) 0xce (by decide)) pre_rip
  have f21 : InstrSpec 0x11491a [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x11491a) (movR64R64Effect 0x11491a 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11491a 0 7).toInstrSpec (mov_r64_r64_effect_step 0x11491a 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x11491d [0x48, 0x0F, 0xC9] (fun s => s.RIP = 0x11491d) (bswapR64Effect 0x11491d 3 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR64Effect_footprint 0x11491d 3 1).toInstrSpec (bswap_r64_effect_step 0x11491d 0x48 (by decide) 0xc9 (by decide)) pre_rip
  have f23 : InstrSpec 0x114920 [0x48, 0x89, 0x17] (StorePre 0x114920 3 (fun s => AddrMode.addr (.base 7 .none) s (0x114920 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x114920 2 (.base 7 .none))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x114920 2 (.base 7 .none)).toInstrSpec (mov_m64_r64_effect_step 0x114920 0x48 (by decide) 2 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x114923 [0x4C, 0x89, 0x57, 0x08] (StorePre 0x114923 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x114923 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x114923 10 (.base 7 (.d8 0x8)))
      [.gpr 10, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x114923 10 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x114923 0x4c (by decide) 2 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x114927 [0x48, 0x89, 0x77, 0x10] (StorePre 0x114927 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x114927 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x114927 6 (.base 7 (.d8 0x10)))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x114927 6 (.base 7 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x114927 0x48 (by decide) 6 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x11492b [0x48, 0x89, 0x4F, 0x18] (StorePre 0x11492b 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x11492b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11492b 1 (.base 7 (.d8 0x18)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x11492b 1 (.base 7 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x11492b 0x48 (by decide) 1 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x11492f [0xC3] (RetPre 0x11492f) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x11492f).toInstrSpec (ret_effect_step 0x11492f) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 67), (1, 65), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11491a) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 65), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11491d) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114920) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114923) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114927) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11492b) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.exec (n := 102) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11492f) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f27 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 104) f27 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 105) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 104), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f27 (by decide) rfl rfl rfl (by decide)

theorem rest_l1148d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1148d0 bytes_l1148d0) (entryMap (live .l1148d0))
      28 0x1148d0 bytes_l1148d0 b_l1148d0 := by
  have f0 : InstrSpec 0x1148d0 [0x48, 0x8B, 0x46, 0x08] (LoadPre 0x1148d0 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1148d0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1148d0 0 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1148d0 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1148d0 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1148d4 [0x4C, 0x8B, 0x46, 0x10] (LoadPre 0x1148d4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1148d4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1148d4 8 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1148d4 8 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1148d4 0x4c (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1148d8 [0x4C, 0x8B, 0x4E, 0x18] (LoadPre 0x1148d8 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1148d8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1148d8 9 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1148d8 9 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1148d8 0x4c (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1148dc [0x48, 0x8B, 0x56, 0x20] (LoadPre 0x1148dc (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1148dc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1148dc 2 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1148dc 2 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1148dc 0x48 (by decide) 2 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1148e0 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x1148e0) (movR64R64Effect 0x1148e0 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1148e0 1 0).toInstrSpec (mov_r64_r64_effect_step 0x1148e0 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1148e3 [0x48, 0xC1, 0xE1, 0x34] (fun s => s.RIP = 0x1148e3) (shlR64Effect 0x1148e3 4 1 52)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x1148e3 4 1 52).toInstrSpec (shl_r64_imm8_effect_step 0x1148e3 0x48 0xe1 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1148e7 [0x48, 0x0B, 0x0E] (LoadPre 0x1148e7 (fun s => AddrMode.addr (.base 6 .none) s (0x1148e7 + BitVec.ofNat 64 3)) 8) (orR64M64Effect 0x1148e7 1 (.base 6 .none))
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (orR64M64Effect_footprint 0x1148e7 1 (.base 6 .none)).toInstrSpec (or_r64_m64_effect_step 0x1148e7 0x48 (by decide) 1 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1148ea [0x48, 0xC1, 0xE8, 0x0C] (fun s => s.RIP = 0x1148ea) (shrR64Effect 0x1148ea 4 0 12)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x1148ea 4 0 12).toInstrSpec (shr_r64_imm8_effect_step 0x1148ea 0x48 0xe8 0xc (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1148ee [0x4C, 0x89, 0xC6] (fun s => s.RIP = 0x1148ee) (movR64R64Effect 0x1148ee 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1148ee 6 8).toInstrSpec (mov_r64_r64_effect_step 0x1148ee 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1148f1 [0x48, 0xC1, 0xE6, 0x28] (fun s => s.RIP = 0x1148f1) (shlR64Effect 0x1148f1 4 6 40)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR64Effect_footprint 0x1148f1 4 6 40).toInstrSpec (shl_r64_imm8_effect_step 0x1148f1 0x48 0xe6 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1148f5 [0x48, 0x09, 0xC6] (fun s => s.RIP = 0x1148f5) (orR64R64Effect 0x1148f5 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1148f5 6 0).toInstrSpec (or_r64_r64_effect_step 0x1148f5 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1148f8 [0x49, 0xC1, 0xE8, 0x18] (fun s => s.RIP = 0x1148f8) (shrR64Effect 0x1148f8 4 8 24)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x1148f8 4 8 24).toInstrSpec (shr_r64_imm8_effect_step 0x1148f8 0x49 0xe8 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1148fc [0x4D, 0x89, 0xCA] (fun s => s.RIP = 0x1148fc) (movR64R64Effect 0x1148fc 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1148fc 10 9).toInstrSpec (mov_r64_r64_effect_step 0x1148fc 0x4d 0xca (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1148ff [0x49, 0xC1, 0xE2, 0x1C] (fun s => s.RIP = 0x1148ff) (shlR64Effect 0x1148ff 4 10 28)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR64Effect_footprint 0x1148ff 4 10 28).toInstrSpec (shl_r64_imm8_effect_step 0x1148ff 0x49 0xe2 0x1c (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x114903 [0x4D, 0x09, 0xC2] (fun s => s.RIP = 0x114903) (orR64R64Effect 0x114903 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (orR64R64Effect_footprint 0x114903 10 8).toInstrSpec (or_r64_r64_effect_step 0x114903 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x114906 [0x49, 0xC1, 0xE9, 0x24] (fun s => s.RIP = 0x114906) (shrR64Effect 0x114906 4 9 36)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x114906 4 9 36).toInstrSpec (shr_r64_imm8_effect_step 0x114906 0x49 0xe9 0x24 (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11490a [0x48, 0xC1, 0xE2, 0x10] (fun s => s.RIP = 0x11490a) (shlR64Effect 0x11490a 4 2 16)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR64Effect_footprint 0x11490a 4 2 16).toInstrSpec (shl_r64_imm8_effect_step 0x11490a 0x48 0xe2 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x11490e [0x4C, 0x09, 0xCA] (fun s => s.RIP = 0x11490e) (orR64R64Effect 0x11490e 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11490e 2 9).toInstrSpec (or_r64_r64_effect_step 0x11490e 0x4c 0xca (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x114911 [0x48, 0x0F, 0xCA] (fun s => s.RIP = 0x114911) (bswapR64Effect 0x114911 3 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR64Effect_footprint 0x114911 3 2).toInstrSpec (bswap_r64_effect_step 0x114911 0x48 (by decide) 0xca (by decide)) pre_rip
  have f19 : InstrSpec 0x114914 [0x49, 0x0F, 0xCA] (fun s => s.RIP = 0x114914) (bswapR64Effect 0x114914 3 10)
      [.gpr 10] [] [.reg 10, .rip] :=
    (bswapR64Effect_footprint 0x114914 3 10).toInstrSpec (bswap_r64_effect_step 0x114914 0x49 (by decide) 0xca (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148d4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148d8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148dc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148e0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 61), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148e3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 63), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148e7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148ea) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148ee) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148f1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 71), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148f5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148f8) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148fc) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 57), (10, 77), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148ff) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 57), (10, 79), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114903) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 57), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114906) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11490a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 67), (1, 65), (2, 85), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11490e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 67), (1, 65), (2, 87), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114911) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 67), (1, 65), (2, 89), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114914) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 67), (1, 65), (2, 89), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114917) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1148d0_1 code

theorem block_l1148d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1148d0 :=
  Rest.liftedBlock (rest_l1148d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1148d0 x hx)

theorem rest_l11c3c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c3c0 bytes_l11c3c0) (entryMap (live .l11c3c0))
      14 0x11c3c0 bytes_l11c3c0 b_l11c3c0 := by
  have f0 : InstrSpec 0x11c3c0 [0x48, 0x8B, 0x4E, 0x18] (LoadPre 0x11c3c0 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x11c3c0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c3c0 1 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11c3c0 1 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x11c3c0 0x48 (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c3c4 [0x48, 0x0F, 0xC9] (fun s => s.RIP = 0x11c3c4) (bswapR64Effect 0x11c3c4 3 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR64Effect_footprint 0x11c3c4 3 1).toInstrSpec (bswap_r64_effect_step 0x11c3c4 0x48 (by decide) 0xc9 (by decide)) pre_rip
  have f2 : InstrSpec 0x11c3c7 [0x48, 0x8B, 0x56, 0x10] (LoadPre 0x11c3c7 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x11c3c7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c3c7 2 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11c3c7 2 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x11c3c7 0x48 (by decide) 2 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11c3cb [0x48, 0x0F, 0xCA] (fun s => s.RIP = 0x11c3cb) (bswapR64Effect 0x11c3cb 3 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR64Effect_footprint 0x11c3cb 3 2).toInstrSpec (bswap_r64_effect_step 0x11c3cb 0x48 (by decide) 0xca (by decide)) pre_rip
  have f4 : InstrSpec 0x11c3ce [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x11c3ce) (movR64R64Effect 0x11c3ce 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c3ce 0 7).toInstrSpec (mov_r64_r64_effect_step 0x11c3ce 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11c3d1 [0x48, 0x8B, 0x7E, 0x08] (LoadPre 0x11c3d1 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x11c3d1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c3d1 7 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x11c3d1 7 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11c3d1 0x48 (by decide) 7 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x11c3d5 [0x48, 0x0F, 0xCF] (fun s => s.RIP = 0x11c3d5) (bswapR64Effect 0x11c3d5 3 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (bswapR64Effect_footprint 0x11c3d5 3 7).toInstrSpec (bswap_r64_effect_step 0x11c3d5 0x48 (by decide) 0xcf (by decide)) pre_rip
  have f7 : InstrSpec 0x11c3d8 [0x48, 0x8B, 0x36] (LoadPre 0x11c3d8 (fun s => AddrMode.addr (.base 6 .none) s (0x11c3d8 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11c3d8 6 (.base 6 .none))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11c3d8 6 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11c3d8 0x48 (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x11c3db [0x48, 0x0F, 0xCE] (fun s => s.RIP = 0x11c3db) (bswapR64Effect 0x11c3db 3 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (bswapR64Effect_footprint 0x11c3db 3 6).toInstrSpec (bswap_r64_effect_step 0x11c3db 0x48 (by decide) 0xce (by decide)) pre_rip
  have f9 : InstrSpec 0x11c3de [0x48, 0x89, 0x08] (StorePre 0x11c3de 3 (fun s => AddrMode.addr (.base 0 .none) s (0x11c3de + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11c3de 1 (.base 0 .none))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c3de 1 (.base 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x11c3de 0x48 (by decide) 1 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x11c3e1 [0x48, 0x89, 0x50, 0x08] (StorePre 0x11c3e1 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x11c3e1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11c3e1 2 (.base 0 (.d8 0x8)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c3e1 2 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11c3e1 0x48 (by decide) 2 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x11c3e5 [0x48, 0x89, 0x78, 0x10] (StorePre 0x11c3e5 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x11c3e5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11c3e5 7 (.base 0 (.d8 0x10)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c3e5 7 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x11c3e5 0x48 (by decide) 7 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x11c3e9 [0x48, 0x89, 0x70, 0x18] (StorePre 0x11c3e9 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x11c3e9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11c3e9 6 (.base 0 (.d8 0x18)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c3e9 6 (.base 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x11c3e9 0x48 (by decide) 6 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x11c3ed [0xC3] (RetPre 0x11c3ed) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x11c3ed).toInstrSpec (ret_effect_step 0x11c3ed) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3c4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3c7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3cb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3ce) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3d1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3d5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3d8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3db) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3de) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3e1) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3e5) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3e9) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3ed) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 76), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f13 (by decide) rfl rfl rfl (by decide)

theorem block_l11c3c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c3c0 :=
  Rest.liftedBlock (rest_l11c3c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c3c0 x hx)

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

theorem_by block_l100180_eval :
    program.runBlock (dialect code) ⟨.l100180, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100185_eval :
    program.runBlock (dialect code) ⟨.l100185, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100191_eval :
    program.runBlock (dialect code) ⟨.l100191, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10019d_eval :
    program.runBlock (dialect code) ⟨.l10019d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10019f_eval :
    program.runBlock (dialect code) ⟨.l10019f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100240_eval :
    program.runBlock (dialect code) ⟨.l100240, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100245_eval :
    program.runBlock (dialect code) ⟨.l100245, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100251_eval :
    program.runBlock (dialect code) ⟨.l100251, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10025d_eval :
    program.runBlock (dialect code) ⟨.l10025d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10025f_eval :
    program.runBlock (dialect code) ⟨.l10025f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100a20_eval :
    program.runBlock (dialect code) ⟨.l100a20, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100a30_eval :
    program.runBlock (dialect code) ⟨.l100a30, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103ec0_eval :
    program.runBlock (dialect code) ⟨.l103ec0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103ed3_eval :
    program.runBlock (dialect code) ⟨.l103ed3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103ee0_eval :
    program.runBlock (dialect code) ⟨.l103ee0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103efa_eval :
    program.runBlock (dialect code) ⟨.l103efa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103f06_eval :
    program.runBlock (dialect code) ⟨.l103f06, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103f0e_eval :
    program.runBlock (dialect code) ⟨.l103f0e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1067b0_eval :
    program.runBlock (dialect code) ⟨.l1067b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106860_eval :
    program.runBlock (dialect code) ⟨.l106860, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106877_eval :
    program.runBlock (dialect code) ⟨.l106877, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106880_eval :
    program.runBlock (dialect code) ⟨.l106880, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10688b_eval :
    program.runBlock (dialect code) ⟨.l10688b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106898_eval :
    program.runBlock (dialect code) ⟨.l106898, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1068d5_eval :
    program.runBlock (dialect code) ⟨.l1068d5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1068e0_eval :
    program.runBlock (dialect code) ⟨.l1068e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1068f1_eval :
    program.runBlock (dialect code) ⟨.l1068f1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108380_eval :
    program.runBlock (dialect code) ⟨.l108380, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1083d3_eval :
    program.runBlock (dialect code) ⟨.l1083d3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1084af_eval :
    program.runBlock (dialect code) ⟨.l1084af, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1084c0_eval :
    program.runBlock (dialect code) ⟨.l1084c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1286b0_eval :
    program.runBlock (dialect code) ⟨.l1286b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1084d0_eval :
    program.runBlock (dialect code) ⟨.l1084d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108890_eval :
    program.runBlock (dialect code) ⟨.l108890, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1088a6_eval :
    program.runBlock (dialect code) ⟨.l1088a6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1088b6_eval :
    program.runBlock (dialect code) ⟨.l1088b6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1088bb_eval :
    program.runBlock (dialect code) ⟨.l1088bb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1088c3_eval :
    program.runBlock (dialect code) ⟨.l1088c3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10893a_eval :
    program.runBlock (dialect code) ⟨.l10893a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108952_eval :
    program.runBlock (dialect code) ⟨.l108952, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10896a_eval :
    program.runBlock (dialect code) ⟨.l10896a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109d80_eval :
    program.runBlock (dialect code) ⟨.l109d80, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109db2_eval :
    program.runBlock (dialect code) ⟨.l109db2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109dcf_eval :
    program.runBlock (dialect code) ⟨.l109dcf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109e30_eval :
    program.runBlock (dialect code) ⟨.l109e30, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109e60_eval :
    program.runBlock (dialect code) ⟨.l109e60, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109f32_eval :
    program.runBlock (dialect code) ⟨.l109f32, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109f60_eval :
    program.runBlock (dialect code) ⟨.l109f60, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109f70_eval :
    program.runBlock (dialect code) ⟨.l109f70, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109f80_eval :
    program.runBlock (dialect code) ⟨.l109f80, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a053_eval :
    program.runBlock (dialect code) ⟨.l10a053, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a05f_eval :
    program.runBlock (dialect code) ⟨.l10a05f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a0c0_eval :
    program.runBlock (dialect code) ⟨.l10a0c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a0f2_eval :
    program.runBlock (dialect code) ⟨.l10a0f2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a10f_eval :
    program.runBlock (dialect code) ⟨.l10a10f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a170_eval :
    program.runBlock (dialect code) ⟨.l10a170, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a211_eval :
    program.runBlock (dialect code) ⟨.l10a211, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a220_eval :
    program.runBlock (dialect code) ⟨.l10a220, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a280_eval :
    program.runBlock (dialect code) ⟨.l10a280, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a293_eval :
    program.runBlock (dialect code) ⟨.l10a293, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a2a0_eval :
    program.runBlock (dialect code) ⟨.l10a2a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a2b3_eval :
    program.runBlock (dialect code) ⟨.l10a2b3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a2bd_eval :
    program.runBlock (dialect code) ⟨.l10a2bd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a2d0_eval :
    program.runBlock (dialect code) ⟨.l10a2d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a2e0_eval :
    program.runBlock (dialect code) ⟨.l10a2e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a2f0_eval :
    program.runBlock (dialect code) ⟨.l10a2f0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fa10_eval :
    program.runBlock (dialect code) ⟨.l10fa10, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fa68_eval :
    program.runBlock (dialect code) ⟨.l10fa68, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fe50_eval :
    program.runBlock (dialect code) ⟨.l10fe50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10ff00_eval :
    program.runBlock (dialect code) ⟨.l10ff00, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10ff24_eval :
    program.runBlock (dialect code) ⟨.l10ff24, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10ff59_eval :
    program.runBlock (dialect code) ⟨.l10ff59, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10ffb3_eval :
    program.runBlock (dialect code) ⟨.l10ffb3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110070_eval :
    program.runBlock (dialect code) ⟨.l110070, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110085_eval :
    program.runBlock (dialect code) ⟨.l110085, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110090_eval :
    program.runBlock (dialect code) ⟨.l110090, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110b80_eval :
    program.runBlock (dialect code) ⟨.l110b80, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1148d0_eval :
    program.runBlock (dialect code) ⟨.l1148d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c3c0_eval :
    program.runBlock (dialect code) ⟨.l11c3c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
