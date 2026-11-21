import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Program
import X86Proofs.Instructions.Branch.Triple
import ChaCha20Poly1305.Proofs.Common.Lift.Generated.Values

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

theorem rest_l1004ac [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1004ac bytes_l1004ac) (entryMap (live .l1004ac))
      3 0x1004ac bytes_l1004ac b_l1004ac := by
  have f0 : InstrSpec 0x1004ac [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x1004ac) (movR64R64Effect 0x1004ac 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1004ac 6 5).toInstrSpec (mov_r64_r64_effect_step 0x1004ac 0x48 0xee (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1004af [0x48, 0x83, 0xC3, 0xF0] (fun s => s.RIP = 0x1004af) (addR64Imm8Effect 0x1004af 3 0xf0)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1004af 3 0xf0).toInstrSpec (add_r64_imm8_effect_step 0x1004af 0x48 0xc3 0xf0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004af) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (3, 55), (4, 4), (5, 5), (6, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004b3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x1004b3 5 0xeb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1004ac [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1004ac :=
  Rest.liftedBlock (rest_l1004ac code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1004ac x hx)

theorem rest_l1004b5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1004b5 bytes_l1004b5) (entryMap (live .l1004b5))
      3 0x1004b5 bytes_l1004b5 b_l1004b5 := by
  have f0 : InstrSpec 0x1004b5 [0x48, 0x8B, 0xAC, 0x24, 0xC0, 0x01, 0x00, 0x00] (LoadPre 0x1004b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x1004b5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1004b5 5 (.sib 4 none 0 (.d32 0x1c0)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x1004b5 5 (.sib 4 none 0 (.d32 0x1c0))).toInstrSpec (mov_r64_m64_effect_step 0x1004b5 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0x1c0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1004bd [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x1004bd) (testR64R64Effect 0x1004bd 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1004bd 14 14).toInstrSpec (test_r64_r64_effect_step 0x1004bd 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004bd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004c0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1004c0 4 0x3a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1004b5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1004b5 :=
  Rest.liftedBlock (rest_l1004b5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1004b5 x hx)

theorem rest_l1004c2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1004c2 bytes_l1004c2) (entryMap (live .l1004c2))
      7 0x1004c2 bytes_l1004c2 b_l1004c2 := by
  have f0 : InstrSpec 0x1004c2 [0x4D, 0x01, 0xFD] (fun s => s.RIP = 0x1004c2) (addR64R64Effect 0x1004c2 13 15)
      [.gpr 13, .gpr 15] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1004c2 13 15).toInstrSpec (add_r64_r64_effect_step 0x1004c2 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1004c5 [0xBA, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1004c5) (movR32Imm32Effect 0x1004c5 5 2 0x10)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1004c5 5 2 0x10).toInstrSpec (mov_r32_imm32_effect_step 0x1004c5 0xba (by decide) 0x10) pre_rip
  have f2 : InstrSpec 0x1004ca [0x4C, 0x29, 0xF2] (fun s => s.RIP = 0x1004ca) (subR64R64Effect 0x1004ca 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1004ca 2 14).toInstrSpec (sub_r64_r64_effect_step 0x1004ca 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1004cd [0x4A, 0x8D, 0x3C, 0x34] (fun s => s.RIP = 0x1004cd) (leaR64Effect 0x1004cd 7 (.sib 4 (some 14) 0 .none))
      [.gpr 4, .gpr 14] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1004cd 7 (.sib 4 (some 14) 0 .none)).toInstrSpec (lea_r64_effect_step 0x1004cd 0x4a (by decide) 7 (.sib 4 (some 14) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1004d1 [0x48, 0x83, 0xC7, 0x20] (fun s => s.RIP = 0x1004d1) (addR64Imm8Effect 0x1004d1 7 0x20)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1004d1 7 0x20).toInstrSpec (add_r64_imm8_effect_step 0x1004d1 0x48 0xc7 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1004d5 [0x31, 0xF6] (fun s => s.RIP = 0x1004d5) (xorR32R32Effect 0x1004d5 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1004d5 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x1004d5 0xf6 (by decide)) pre_rip
  have f6 : InstrSpec 0x1004d7 [0xFF, 0x15, 0x03, 0x0F, 0x10, 0x00] (GoesTo (CallMemPre 0x1004d7 (.rip 0x100f03)) (callEffect (callMemPtr 0x1004d7 (.rip 0x100f03)) (0x1004d7 + BitVec.ofNat 64 (callMemLen (.rip 0x100f03)))) 0x102d70) (callEffect (callMemPtr 0x1004d7 (.rip 0x100f03)) (0x1004d7 + BitVec.ofNat 64 (callMemLen (.rip 0x100f03))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1004d7 (.rip 0x100f03)).toInstrSpec (call_m64_effect_step 0x1004d7 (.rip 0x100f03) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x102d70
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004c5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004ca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004cd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 59), (9, 9), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004d1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 61), (9, 9), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004d5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 61), (9, 9), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004d7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 57), (3, 3), (4, 65), (5, 5), (6, 63), (7, 61), (9, 9), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d70) f6 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l1004c2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1004c2 :=
  Rest.liftedBlock (rest_l1004c2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1004c2 x hx)

theorem rest_l1004dd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1004dd bytes_l1004dd) (entryMap (live .l1004dd))
      5 0x1004dd bytes_l1004dd b_l1004dd := by
  have f0 : InstrSpec 0x1004dd [0x48, 0x8D, 0x5C, 0x24, 0x20] (fun s => s.RIP = 0x1004dd) (leaR64Effect 0x1004dd 3 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x1004dd 3 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x1004dd 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1004e2 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x1004e2) (movR64R64Effect 0x1004e2 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1004e2 7 3).toInstrSpec (mov_r64_r64_effect_step 0x1004e2 0x48 0xdf (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1004e5 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x1004e5) (movR64R64Effect 0x1004e5 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1004e5 6 13).toInstrSpec (mov_r64_r64_effect_step 0x1004e5 0x4c 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1004e8 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x1004e8) (movR64R64Effect 0x1004e8 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1004e8 2 14).toInstrSpec (mov_r64_r64_effect_step 0x1004e8 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1004eb [0xFF, 0x15, 0xB7, 0x0E, 0x10, 0x00] (GoesTo (CallMemPre 0x1004eb (.rip 0x100eb7)) (callEffect (callMemPtr 0x1004eb (.rip 0x100eb7)) (0x1004eb + BitVec.ofNat 64 (callMemLen (.rip 0x100eb7)))) 0x102dc0) (callEffect (callMemPtr 0x1004eb (.rip 0x100eb7)) (0x1004eb + BitVec.ofNat 64 (callMemLen (.rip 0x100eb7))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1004eb (.rip 0x100eb7)).toInstrSpec (call_m64_effect_step 0x1004eb (.rip 0x100eb7) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x102dc0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004e2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004e5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004e8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 53), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004eb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 53), (4, 61), (5, 5), (6, 57), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dc0) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l1004dd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1004dd :=
  Rest.liftedBlock (rest_l1004dd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1004dd x hx)

theorem rest_l1004f1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1004f1 bytes_l1004f1) (entryMap (live .l1004f1))
      3 0x1004f1 bytes_l1004f1 b_l1004f1 := by
  have f0 : InstrSpec 0x1004f1 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x1004f1) (movR64R64Effect 0x1004f1 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1004f1 7 12).toInstrSpec (mov_r64_r64_effect_step 0x1004f1 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1004f4 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x1004f4) (movR64R64Effect 0x1004f4 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1004f4 6 3).toInstrSpec (mov_r64_r64_effect_step 0x1004f4 0x48 0xde (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1004f7 [0xE8, 0x34, 0x19, 0x00, 0x00] (PushPre 0x1004f7 5) (callEffect (fun _ => 0x101e30) 0x1004fc)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1004f7 0x101e30 0x1004fc).toInstrSpec (call_rel32_effect_step 0x1004f7 0x1934 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004f4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004f7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e30) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l1004f1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1004f1 :=
  Rest.liftedBlock (rest_l1004f1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1004f1 x hx)

theorem rest_l1004fc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1004fc bytes_l1004fc) (entryMap (live .l1004fc))
      7 0x1004fc bytes_l1004fc b_l1004fc := by
  have f0 : InstrSpec 0x1004fc [0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x1004fc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1004fc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1004fc 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1004fc 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x1004fc 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100504 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x100504 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100504 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100504 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100504 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x100504 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x100509 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x100509 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100509 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100509 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100509 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x100509 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10050e [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x10050e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10050e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10050e 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10050e 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10050e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x100513 [0x48, 0x8D, 0x74, 0x24, 0x20] (fun s => s.RIP = 0x100513) (leaR64Effect 0x100513 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x100513 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x100513 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x100518 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x100518) (movR64R64Effect 0x100518 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x100518 7 12).toInstrSpec (mov_r64_r64_effect_step 0x100518 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10051b [0xE8, 0x10, 0x19, 0x00, 0x00] (PushPre 0x10051b 5) (callEffect (fun _ => 0x101e30) 0x100520)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10051b 0x101e30 0x100520).toInstrSpec (call_rel32_effect_step 0x10051b 0x1910 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100504) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100509) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10050e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100513) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100518) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10051b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 63), (5, 5), (6, 59), (7, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e30) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l1004fc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1004fc :=
  Rest.liftedBlock (rest_l1004fc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1004fc x hx)

theorem rest_l100520 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100520 bytes_l100520) (entryMap (live .l100520))
      17 0x100520 bytes_l100520 b_l100520 := by
  have f0 : InstrSpec 0x100520 [0x49, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x100520 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x30)) s (0x100520 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100520 0 (.sib 12 none 0 (.d8 0x30)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100520 0 (.sib 12 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x100520 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100525 [0x48, 0x89, 0x44, 0x24, 0x50] (StorePre 0x100525 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x100525 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100525 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100525 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x100525 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10052a [0x49, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x10052a (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x28)) s (0x10052a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10052a 0 (.sib 12 none 0 (.d8 0x28)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10052a 0 (.sib 12 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10052a 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10052f [0x48, 0x89, 0x44, 0x24, 0x48] (StorePre 0x10052f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10052f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10052f 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10052f 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x10052f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x100534 [0x49, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x100534 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x20)) s (0x100534 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100534 0 (.sib 12 none 0 (.d8 0x20)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100534 0 (.sib 12 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x100534 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x100539 [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x100539 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100539 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100539 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100539 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x100539 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10053e [0x49, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x10053e (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x10053e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10053e 0 (.sib 12 none 0 (.d8 0x18)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10053e 0 (.sib 12 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10053e 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x100543 [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x100543 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x100543 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100543 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100543 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x100543 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x100548 [0x49, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x100548 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x100548 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100548 0 (.sib 12 none 0 (.d8 0x10)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100548 0 (.sib 12 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x100548 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10054d [0x48, 0x89, 0x44, 0x24, 0x30] (StorePre 0x10054d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10054d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10054d 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10054d 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10054d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x100552 [0x49, 0x8B, 0x04, 0x24] (LoadPre 0x100552 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x100552 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100552 0 (.sib 12 none 0 .none))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100552 0 (.sib 12 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x100552 0x49 (by decide) 0 (.sib 12 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x100556 [0x49, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x100556 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x100556 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100556 1 (.sib 12 none 0 (.d8 0x8)))
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100556 1 (.sib 12 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x100556 0x49 (by decide) 1 (.sib 12 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x10055b [0x48, 0x89, 0x4C, 0x24, 0x28] (StorePre 0x10055b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10055b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10055b 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10055b 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10055b 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x100560 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x100560 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100560 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100560 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100560 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x100560 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x100565 [0x48, 0x8D, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100565) (leaR64Effect 0x100565 7 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x100565 7 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x100565 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10056d [0x48, 0x8D, 0x74, 0x24, 0x20] (fun s => s.RIP = 0x10056d) (leaR64Effect 0x10056d 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10056d 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x10056d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x100572 [0xE8, 0x69, 0x17, 0x00, 0x00] (PushPre 0x100572 5) (callEffect (fun _ => 0x101ce0) 0x100577)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100572 0x101ce0 0x100577).toInstrSpec (call_rel32_effect_step 0x100572 0x1769 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100525) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10052a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10052f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100534) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100539) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10053e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100543) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100548) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10054d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100552) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100556) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 68), (1, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10055b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 68), (1, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100560) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 68), (1, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100565) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 68), (1, 70), (3, 3), (4, 4), (5, 5), (7, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10056d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 68), (1, 70), (3, 3), (4, 4), (5, 5), (6, 76), (7, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100572) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 68), (1, 70), (3, 3), (4, 78), (5, 5), (6, 76), (7, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ce0) f16 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 80) (by decide) (by decide) rfl rfl

theorem block_l100520 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100520 :=
  Rest.liftedBlock (rest_l100520 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100520 x hx)

theorem rest_l100577_1 [Bindings] (code : CodeMap) :
    Rest (n := 95) code lifted (codeRange 0x100577 bytes_l100577) [(0, 93), (1, 59), (2, 87), (3, 3), (4, 4), (5, 5), (6, 80), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 88), (22, 22), (39, 39), (50, 50), (51, 51)]
      3 0x1005c9 bytes_l100577_1 b_l100577_1 := by
  have f20 : InstrSpec 0x1005c9 [0x80, 0x7C, 0x24, 0x06, 0x00] (LoadPre 0x1005c9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1005c9 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x1005c9 5 (.sib 4 none 0 (.d8 0x6)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x1005c9 5 (.sib 4 none 0 (.d8 0x6)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x1005c9 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x1005ce [0xB0, 0x01] (fun s => s.RIP = 0x1005ce) (movR8Imm8Effect 0x1005ce 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x1005ce 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x1005ce 0xb0 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f20 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 93), (1, 59), (2, 87), (3, 3), (4, 4), (5, 5), (6, 80), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005ce) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 97), (1, 59), (2, 87), (3, 3), (4, 4), (5, 5), (6, 80), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005d0) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 99) (jcc_rel8_effect_step 0x1005d0 4 0x18) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l100577 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100577 bytes_l100577) (entryMap (live .l100577))
      23 0x100577 bytes_l100577 b_l100577 := by
  have f0 : InstrSpec 0x100577 [0x48, 0x8B, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x100577 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x100577 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100577 2 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x100577 2 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x100577 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10057f [0x48, 0x8B, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x10057f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10057f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10057f 6 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10057f 6 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x10057f 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100587 [0x31, 0xC0] (fun s => s.RIP = 0x100587) (xorR32R32Effect 0x100587 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100587 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x100587 0xc0 (by decide)) pre_rip
  have f3 : InstrSpec 0x100589 [0x66, 0xB9, 0x01, 0x00] (fun s => s.RIP = 0x100589) (movR16Imm16Effect 0x100589 4 1 0x1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR16Imm16Effect_footprint 0x100589 4 1 0x1).toInstrSpec (mov_r16_imm16_effect_step 0x100589 0xb9 (by decide) 0x1) pre_rip
  have f4 : InstrSpec 0x10058d [0x66, 0xBF, 0x01, 0x00] (fun s => s.RIP = 0x10058d) (movR16Imm16Effect 0x10058d 4 7 0x1)
      [.gpr 7] [] [.reg 7, .rip] :=
    (movR16Imm16Effect_footprint 0x10058d 4 7 0x1).toInstrSpec (mov_r16_imm16_effect_step 0x10058d 0xbf (by decide) 0x1) pre_rip
  have f5 : InstrSpec 0x100591 [0x4C, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x100591 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x100591 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100591 8 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x100591 8 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x100591 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x100599 [0x4C, 0x31, 0xC2] (fun s => s.RIP = 0x100599) (xorR64R64Effect 0x100599 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100599 2 8).toInstrSpec (xor_r64_r64_effect_step 0x100599 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10059c [0x48, 0x0F, 0x45, 0xF8] (fun s => s.RIP = 0x10059c) (atFlags (condHolds 5) (cmovR64R64Effect 0x10059c 4 7 0))
      [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (cmovR64R64Effect_footprint 0x10059c 4 7 0 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10059c 5 0x48 (by decide) 0xf8 (by decide) c)) pre_rip
  have f8 : InstrSpec 0x1005a0 [0x40, 0x0F, 0xB6, 0xD7] (fun s => s.RIP = 0x1005a0) (movzxR32R8Effect 0x1005a0 4 2 7)
      [.gpr 7] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x1005a0 4 2 7).toInstrSpec (movzx_r32_r8_rex_effect_step 0x1005a0 0x40 (by decide) 0xd7 (by decide)) pre_rip
  have f9 : InstrSpec 0x1005a4 [0x48, 0x31, 0xEE] (fun s => s.RIP = 0x1005a4) (xorR64R64Effect 0x1005a4 6 5)
      [.gpr 6, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1005a4 6 5).toInstrSpec (xor_r64_r64_effect_step 0x1005a4 0x48 0xee (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1005a7 [0x48, 0x0F, 0x45, 0xD0] (fun s => s.RIP = 0x1005a7) (atFlags (condHolds 5) (cmovR64R64Effect 0x1005a7 4 2 0))
      [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x1005a7 4 2 0 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x1005a7 5 0x48 (by decide) 0xd0 (by decide) c)) pre_rip
  have f11 : InstrSpec 0x1005ab [0x0F, 0xB6, 0xD2] (fun s => s.RIP = 0x1005ab) (movzxR32R8Effect 0x1005ab 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x1005ab 3 2 2).toInstrSpec (movzx_r32_r8_effect_step 0x1005ab 0xd2 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1005ae [0x31, 0xF6] (fun s => s.RIP = 0x1005ae) (xorR32R32Effect 0x1005ae 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1005ae 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x1005ae 0xf6 (by decide)) pre_rip
  have f13 : InstrSpec 0x1005b0 [0x48, 0x31, 0xC6] (fun s => s.RIP = 0x1005b0) (xorR64R64Effect 0x1005b0 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1005b0 6 0).toInstrSpec (xor_r64_r64_effect_step 0x1005b0 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1005b3 [0x48, 0x0F, 0x45, 0xD0] (fun s => s.RIP = 0x1005b3) (atFlags (condHolds 5) (cmovR64R64Effect 0x1005b3 4 2 0))
      [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x1005b3 4 2 0 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x1005b3 5 0x48 (by decide) 0xd0 (by decide) c)) pre_rip
  have f15 : InstrSpec 0x1005b7 [0x0F, 0xB6, 0xD2] (fun s => s.RIP = 0x1005b7) (movzxR32R8Effect 0x1005b7 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x1005b7 3 2 2).toInstrSpec (movzx_r32_r8_effect_step 0x1005b7 0xd2 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1005ba [0x66, 0x31, 0xCA] (fun s => s.RIP = 0x1005ba) (xorR16R16Effect 0x1005ba 3 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR16R16Effect_footprint 0x1005ba 3 2 1).toInstrSpec (xor_r16_r16_effect_step 0x1005ba 0xca (by decide)) pre_rip
  have f17 : InstrSpec 0x1005bd [0x0F, 0x44, 0xC1] (fun s => s.RIP = 0x1005bd) (atFlags (condHolds 4) (cmovR32R32Effect 0x1005bd 3 0 1))
      [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (cmovR32R32Effect_footprint 0x1005bd 3 0 1 4).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_effect_step 0x1005bd 4 0xc1 (by decide) c)) pre_rip
  have f18 : InstrSpec 0x1005c0 [0x88, 0x44, 0x24, 0x06] (StorePre 0x1005c0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1005c0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1005c0 4 0 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1005c0 4 0 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (mov_m8_r8_effect_step 0x1005c0 0 (by decide) (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1005c4 [0x48, 0x8D, 0x44, 0x24, 0x06] (fun s => s.RIP = 0x1005c4) (leaR64Effect 0x1005c4 0 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1005c4 0 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (lea_r64_effect_step 0x1005c4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10057f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100587) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100589) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10058d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 59), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 61), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100591) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 59), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 61), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100599) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (6, 55), (7, 61), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10059c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (6, 55), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005a0) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 57), (1, 59), (2, 69), (3, 3), (4, 4), (5, 5), (6, 55), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005a4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f9 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 57), (1, 59), (2, 69), (3, 3), (4, 4), (5, 5), (6, 71), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005a7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 57), (1, 59), (2, 74), (3, 3), (4, 4), (5, 5), (6, 71), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005ab) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 57), (1, 59), (2, 76), (3, 3), (4, 4), (5, 5), (6, 71), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005ae) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 57), (1, 59), (2, 76), (3, 3), (4, 4), (5, 5), (6, 78), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005b0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 81) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 82) (ρ' := [(0, 57), (1, 59), (2, 76), (3, 3), (4, 4), (5, 5), (6, 80), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005b3) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 57), (1, 59), (2, 83), (3, 3), (4, 4), (5, 5), (6, 80), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005b7) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 57), (1, 59), (2, 85), (3, 3), (4, 4), (5, 5), (6, 80), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005ba) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 88) f16 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 89) (ρ' := [(0, 57), (1, 59), (2, 87), (3, 3), (4, 4), (5, 5), (6, 80), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005bd) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 90), (1, 59), (2, 87), (3, 3), (4, 4), (5, 5), (6, 80), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005c0) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 90), (1, 59), (2, 87), (3, 3), (4, 4), (5, 5), (6, 80), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005c4) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 93), (1, 59), (2, 87), (3, 3), (4, 4), (5, 5), (6, 80), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005c9) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100577_1 code

theorem block_l100577 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100577 :=
  Rest.liftedBlock (rest_l100577 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100577 x hx)

theorem rest_l1005d2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1005d2 bytes_l1005d2) (entryMap (live .l1005d2))
      3 0x1005d2 bytes_l1005d2 b_l1005d2 := by
  have f0 : InstrSpec 0x1005d2 [0x48, 0x8D, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1005d2) (leaR64Effect 0x1005d2 7 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1005d2 7 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (lea_r64_effect_step 0x1005d2 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1005da [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x1005da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1005da + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1005da 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1005da 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1005da 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1005df [0xE8, 0x9C, 0x04, 0x00, 0x00] (PushPre 0x1005df 5) (callEffect (fun _ => 0x100a80) 0x1005e4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1005df 0x100a80 0x1005e4).toInstrSpec (call_rel32_effect_step 0x1005df 0x49c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005da) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005df) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a80) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l1005d2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1005d2 :=
  Rest.liftedBlock (rest_l1005d2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1005d2 x hx)

theorem rest_l1005e4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1005e4 bytes_l1005e4) (entryMap (live .l1005e4))
      2 0x1005e4 bytes_l1005e4 b_l1005e4 := by
  have f0 : InstrSpec 0x1005e4 [0x84, 0xC0] (fun s => s.RIP = 0x1005e4) (testR8R8Effect 0x1005e4 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1005e4 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x1005e4 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005e6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1005e6 5 0x38) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1005e4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1005e4 :=
  Rest.liftedBlock (rest_l1005e4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1005e4 x hx)

theorem rest_l1005e8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1005e8 bytes_l1005e8) (entryMap (live .l1005e8))
      1 0x1005e8 bytes_l1005e8 b_l1005e8 := by
  have f0 : InstrSpec 0x1005e8 [0x31, 0xC0] (fun s => s.RIP = 0x1005e8) (xorR32R32Effect 0x1005e8 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1005e8 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x1005e8 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005ea) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1005e8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1005e8 :=
  Rest.liftedBlock (rest_l1005e8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1005e8 x hx)

theorem rest_l1005ea [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1005ea bytes_l1005ea) (entryMap (live .l1005ea))
      8 0x1005ea bytes_l1005ea b_l1005ea := by
  have f0 : InstrSpec 0x1005ea [0x48, 0x81, 0xC4, 0x88, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1005ea) (addR64Imm32Effect 0x1005ea 4 0x188)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x1005ea 4 0x188).toInstrSpec (add_r64_imm32_effect_step 0x1005ea 0x48 0xc4 0x188 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1005f1 [0x5B] (PopPre 0x1005f1) (popR64Effect 0x1005f1 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1005f1 1 3).toInstrSpec (pop_r64_effect_step 0x1005f1 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1005f2 [0x41, 0x5C] (PopPre 0x1005f2) (popR64Effect 0x1005f2 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1005f2 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1005f2 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1005f4 [0x41, 0x5D] (PopPre 0x1005f4) (popR64Effect 0x1005f4 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1005f4 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1005f4 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1005f6 [0x41, 0x5E] (PopPre 0x1005f6) (popR64Effect 0x1005f6 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1005f6 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1005f6 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1005f8 [0x41, 0x5F] (PopPre 0x1005f8) (popR64Effect 0x1005f8 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1005f8 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1005f8 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1005fa [0x5D] (PopPre 0x1005fa) (popR64Effect 0x1005fa 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1005fa 1 5).toInstrSpec (pop_r64_effect_step 0x1005fa 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1005fb [0xC3] (RetPre 0x1005fb) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1005fb).toInstrSpec (ret_effect_step 0x1005fb) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005f1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005f2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (9, 9), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005f4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005f6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005f8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005fa) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005fb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l1005ea [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1005ea :=
  Rest.liftedBlock (rest_l1005ea code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1005ea x hx)

theorem rest_l1005fc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1005fc bytes_l1005fc) (entryMap (live .l1005fc))
      0 0x1005fc bytes_l1005fc b_l1005fc := by
  exact Rest.cut

theorem block_l1005fc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1005fc :=
  Rest.liftedBlock (rest_l1005fc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1005fc x hx)

theorem rest_l100620 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100620 bytes_l100620) (entryMap (live .l100620))
      0 0x100620 bytes_l100620 b_l100620 := by
  exact Rest.cut

theorem block_l100620 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100620 :=
  Rest.liftedBlock (rest_l100620 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100620 x hx)

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

theorem_by block_l1004ac_eval :
    program.runBlock (dialect code) ⟨.l1004ac, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1004b5_eval :
    program.runBlock (dialect code) ⟨.l1004b5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1004c2_eval :
    program.runBlock (dialect code) ⟨.l1004c2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1004dd_eval :
    program.runBlock (dialect code) ⟨.l1004dd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1004f1_eval :
    program.runBlock (dialect code) ⟨.l1004f1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1004fc_eval :
    program.runBlock (dialect code) ⟨.l1004fc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100520_eval :
    program.runBlock (dialect code) ⟨.l100520, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100577_eval :
    program.runBlock (dialect code) ⟨.l100577, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1005d2_eval :
    program.runBlock (dialect code) ⟨.l1005d2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1005e4_eval :
    program.runBlock (dialect code) ⟨.l1005e4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1005e8_eval :
    program.runBlock (dialect code) ⟨.l1005e8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1005ea_eval :
    program.runBlock (dialect code) ⟨.l1005ea, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1005fc_eval :
    program.runBlock (dialect code) ⟨.l1005fc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100620_eval :
    program.runBlock (dialect code) ⟨.l100620, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
