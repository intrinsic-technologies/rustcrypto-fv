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

theorem rest_l1286fc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1286fc bytes_l1286fc) (entryMap (live .l1286fc))
      4 0x1286fc bytes_l1286fc b_l1286fc := by
  have f0 : InstrSpec 0x1286fc [0x55] (PushPre 0x1286fc 1) (pushR64Effect 0x1286fc 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1286fc 1 5).toInstrSpec (push_r64_effect_step 0x1286fc 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1286fd [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x1286fd) (movR64R64Effect 0x1286fd 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x1286fd 5 4).toInstrSpec (mov_r64_r64_effect_step 0x1286fd 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128700 [0x48, 0x85, 0xFF] (fun s => s.RIP = 0x128700) (testR64R64Effect 0x128700 7 7)
      [.gpr 7, .gpr 7] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x128700 7 7).toInstrSpec (test_r64_r64_effect_step 0x128700 0x48 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 53), (5, 5), (6, 6), (7, 7)]) (p' := 0x1286fd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 53), (5, 55), (6, 6), (7, 7)]) (p' := 0x128700) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 53), (5, 55), (6, 6), (7, 7), (19, 57)]) (p' := 0x128703) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x128703 5 0x6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1286fc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1286fc :=
  Rest.liftedBlock (rest_l1286fc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1286fc x hx)

theorem rest_l128705 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128705 bytes_l128705) (entryMap (live .l128705))
      1 0x128705 bytes_l128705 b_l128705 := by
  have f0 : InstrSpec 0x128705 [0xFF, 0x15, 0xB5, 0xB6, 0x0D, 0x00] (GoesTo (CallMemPre 0x128705 (.rip 0xdb6b5)) (callEffect (callMemPtr 0x128705 (.rip 0xdb6b5)) (0x128705 + BitVec.ofNat 64 (callMemLen (.rip 0xdb6b5)))) 0x128720) (callEffect (callMemPtr 0x128705 (.rip 0xdb6b5)) (0x128705 + BitVec.ofNat 64 (callMemLen (.rip 0xdb6b5))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x128705 (.rip 0xdb6b5)).toInstrSpec (call_m64_effect_step 0x128705 (.rip 0xdb6b5) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x128720
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 53), (5, 5)]) (p' := 0x128720) f0 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 55) (by decide) (by decide) rfl rfl

theorem block_l128705 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128705 :=
  Rest.liftedBlock (rest_l128705 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128705 x hx)

theorem rest_l12870b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12870b bytes_l12870b) (entryMap (live .l12870b))
      1 0x12870b bytes_l12870b b_l12870b := by
  have f0 : InstrSpec 0x12870b [0xFF, 0x15, 0xC7, 0xB6, 0x0D, 0x00] (GoesTo (CallMemPre 0x12870b (.rip 0xdb6c7)) (callEffect (callMemPtr 0x12870b (.rip 0xdb6c7)) (0x12870b + BitVec.ofNat 64 (callMemLen (.rip 0xdb6c7)))) 0x1286e9) (callEffect (callMemPtr 0x12870b (.rip 0xdb6c7)) (0x12870b + BitVec.ofNat 64 (callMemLen (.rip 0xdb6c7))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x12870b (.rip 0xdb6c7)).toInstrSpec (call_m64_effect_step 0x12870b (.rip 0xdb6c7) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x1286e9
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 53), (5, 5), (6, 6), (7, 7)]) (p' := 0x1286e9) f0 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 55) (by decide) (by decide) rfl rfl

theorem block_l12870b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12870b :=
  Rest.liftedBlock (rest_l12870b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12870b x hx)

theorem rest_l128711 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128711 bytes_l128711) (entryMap (live .l128711))
      2 0x128711 bytes_l128711 b_l128711 := by
  have f0 : InstrSpec 0x128711 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128711) (fun _ => nopEffect 0x128711 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x128711 10).toInstrSpec (nop_m_effect_step 0x128711 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12871b [0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x12871b) (fun _ => nopEffect 0x12871b 5)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12871b 5).toInstrSpec (nop_m_effect_step 0x12871b [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x12871b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5)]) (p' := 0x128720) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l128711 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128711 :=
  Rest.liftedBlock (rest_l128711 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128711 x hx)

theorem rest_l128720 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128720 bytes_l128720) (entryMap (live .l128720))
      6 0x128720 bytes_l128720 b_l128720 := by
  have f0 : InstrSpec 0x128720 [0x55] (PushPre 0x128720 1) (pushR64Effect 0x128720 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128720 1 5).toInstrSpec (push_r64_effect_step 0x128720 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x128721 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x128721) (movR64R64Effect 0x128721 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x128721 5 4).toInstrSpec (mov_r64_r64_effect_step 0x128721 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128724 [0x48, 0x8D, 0x3D, 0x16, 0xB4, 0x0D, 0x00] (fun s => s.RIP = 0x128724) (leaR64Effect 0x128724 7 (.rip 0xdb416))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x128724 7 (.rip 0xdb416)).toInstrSpec (lea_r64_effect_step 0x128724 0x48 (by decide) 7 (.rip 0xdb416) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12872b [0x48, 0x8D, 0x15, 0x1E, 0xB6, 0x0D, 0x00] (fun s => s.RIP = 0x12872b) (leaR64Effect 0x12872b 2 (.rip 0xdb61e))
      [] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x12872b 2 (.rip 0xdb61e)).toInstrSpec (lea_r64_effect_step 0x12872b 0x48 (by decide) 2 (.rip 0xdb61e) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x128732 [0xBE, 0x23, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128732) (movR32Imm32Effect 0x128732 5 6 0x23)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x128732 5 6 0x23).toInstrSpec (mov_r32_imm32_effect_step 0x128732 0xbe (by decide) 0x23) pre_rip
  have f5 : InstrSpec 0x128737 [0xFF, 0x15, 0xA3, 0xB6, 0x0D, 0x00] (GoesTo (CallMemPre 0x128737 (.rip 0xdb6a3)) (callEffect (callMemPtr 0x128737 (.rip 0xdb6a3)) (0x128737 + BitVec.ofNat 64 (callMemLen (.rip 0xdb6a3)))) 0x129770) (callEffect (callMemPtr 0x128737 (.rip 0xdb6a3)) (0x128737 + BitVec.ofNat 64 (callMemLen (.rip 0xdb6a3))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x128737 (.rip 0xdb6a3)).toInstrSpec (call_m64_effect_step 0x128737 (.rip 0xdb6a3) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 53), (5, 5)]) (p' := 0x128721) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 53), (5, 55)]) (p' := 0x128724) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(4, 53), (5, 55), (7, 57)]) (p' := 0x12872b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (4, 53), (5, 55), (7, 57)]) (p' := 0x128732) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (4, 53), (5, 55), (6, 61), (7, 57)]) (p' := 0x128737) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 59), (4, 63), (5, 55), (6, 61), (7, 57)]) (p' := 0x129770) f5 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l128720 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128720 :=
  Rest.liftedBlock (rest_l128720 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128720 x hx)

theorem rest_l128a40 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a40 bytes_l128a40) (entryMap (live .l128a40))
      4 0x128a40 bytes_l128a40 b_l128a40 := by
  have f0 : InstrSpec 0x128a40 [0x48, 0x8B, 0x17] (LoadPre 0x128a40 (fun s => AddrMode.addr (.base 7 .none) s (0x128a40 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128a40 2 (.base 7 .none))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x128a40 2 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128a40 0x48 (by decide) 2 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128a43 [0x0F, 0xB6, 0x4F, 0x10] (LoadPre 0x128a43 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x128a43 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x128a43 4 1 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x128a43 4 1 (.base 7 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x128a43 1 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128a47 [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x128a47) (testR64R64Effect 0x128a47 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x128a47 2 2).toInstrSpec (test_r64_r64_effect_step 0x128a47 0x48 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a43) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a47) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a4a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x128a4a 4 0x72) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128a40 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a40 :=
  Rest.liftedBlock (rest_l128a40 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a40 x hx)

theorem rest_l128a4c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a4c bytes_l128a4c) (entryMap (live .l128a4c))
      3 0x128a4c bytes_l128a4c b_l128a4c := by
  have f0 : InstrSpec 0x128a4c [0xB0, 0x01] (fun s => s.RIP = 0x128a4c) (movR8Imm8Effect 0x128a4c 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x128a4c 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x128a4c 0xb0 (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x128a4e [0x84, 0xC9] (fun s => s.RIP = 0x128a4e) (testR8R8Effect 0x128a4e 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128a4e 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x128a4e 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a4e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a50) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x128a50 5 0x67) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128a4c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a4c :=
  Rest.liftedBlock (rest_l128a4c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a4c x hx)

theorem rest_l128a52 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a52 bytes_l128a52) (entryMap (live .l128a52))
      7 0x128a52 bytes_l128a52 b_l128a52 := by
  have f0 : InstrSpec 0x128a52 [0x55] (PushPre 0x128a52 1) (pushR64Effect 0x128a52 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128a52 1 5).toInstrSpec (push_r64_effect_step 0x128a52 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x128a53 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x128a53) (movR64R64Effect 0x128a53 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x128a53 5 4).toInstrSpec (mov_r64_r64_effect_step 0x128a53 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128a56 [0x41, 0x56] (PushPre 0x128a56 2) (pushR64Effect 0x128a56 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128a56 2 14).toInstrSpec (push_r64_rex_effect_step 0x128a56 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x128a58 [0x53] (PushPre 0x128a58 1) (pushR64Effect 0x128a58 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128a58 1 3).toInstrSpec (push_r64_effect_step 0x128a58 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x128a59 [0x48, 0x8B, 0x5F, 0x08] (LoadPre 0x128a59 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x128a59 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128a59 3 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x128a59 3 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x128a59 0x48 (by decide) 3 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x128a5d [0x48, 0x83, 0xFA, 0x01] (fun s => s.RIP = 0x128a5d) (cmpR64Imm8Effect 0x128a5d 2 0x1)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x128a5d 2 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x128a5d 0x48 0xfa 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (7, 7), (14, 14)]) (p' := 0x128a53) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(2, 2), (3, 3), (4, 53), (7, 7), (14, 14)]) (p' := 0x128a56) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (3, 3), (4, 56), (7, 7), (14, 14)]) (p' := 0x128a58) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (7, 7), (14, 14)]) (p' := 0x128a59) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 59), (7, 7), (14, 14)]) (p' := 0x128a5d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 59), (7, 7), (14, 14), (19, 61)]) (p' := 0x128a61) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x128a61 5 0x33) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128a52 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a52 :=
  Rest.liftedBlock (rest_l128a52 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a52 x hx)

theorem rest_l128a63 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a63 bytes_l128a63) (entryMap (live .l128a63))
      2 0x128a63 bytes_l128a63 b_l128a63 := by
  have f0 : InstrSpec 0x128a63 [0x80, 0x7F, 0x11, 0x00] (LoadPre 0x128a63 (fun s => AddrMode.addr (.base 7 (.d8 0x11)) s (0x128a63 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x128a63 4 (.base 7 (.d8 0x11)) 0x0)
      [.gpr 7] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x128a63 4 (.base 7 (.d8 0x11)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x128a63 (.base 7 (.d8 0x11)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (7, 7), (19, 53)]) (p' := 0x128a67) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128a67 4 0x2d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128a63 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a63 :=
  Rest.liftedBlock (rest_l128a63 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a63 x hx)

theorem rest_l128a69 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a69 bytes_l128a69) (entryMap (live .l128a69))
      2 0x128a69 bytes_l128a69 b_l128a69 := by
  have f0 : InstrSpec 0x128a69 [0xF6, 0x43, 0x12, 0x80] (LoadPre 0x128a69 (fun s => AddrMode.addr (.base 3 (.d8 0x12)) s (0x128a69 + BitVec.ofNat 64 4)) 1) (testM8Imm8Effect 0x128a69 4 (.base 3 (.d8 0x12)) 0x80)
      [.gpr 3] [] [.flags, .rip] :=
    (testM8Imm8Effect_footprint 0x128a69 4 (.base 3 (.d8 0x12)) 0x80).toInstrSpec (test_m8_imm8_effect_step 0x128a69 (.base 3 (.d8 0x12)) (by decide) (by decide) (by decide) 0x80) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (7, 7), (19, 53)]) (p' := 0x128a6d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128a6d 5 0x27) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128a69 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a69 :=
  Rest.liftedBlock (rest_l128a69 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a69 x hx)

theorem rest_l128a6f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a6f bytes_l128a6f) (entryMap (live .l128a6f))
      6 0x128a6f bytes_l128a6f b_l128a6f := by
  have f0 : InstrSpec 0x128a6f [0x48, 0x8B, 0x03] (LoadPre 0x128a6f (fun s => AddrMode.addr (.base 3 .none) s (0x128a6f + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128a6f 0 (.base 3 .none))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128a6f 0 (.base 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128a6f 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128a72 [0x48, 0x8B, 0x4B, 0x08] (LoadPre 0x128a72 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x128a72 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128a72 1 (.base 3 (.d8 0x8)))
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x128a72 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x128a72 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128a76 [0x48, 0x8D, 0x35, 0xB8, 0xB1, 0x0D, 0x00] (fun s => s.RIP = 0x128a76) (leaR64Effect 0x128a76 6 (.rip 0xdb1b8))
      [] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x128a76 6 (.rip 0xdb1b8)).toInstrSpec (lea_r64_effect_step 0x128a76 0x48 (by decide) 6 (.rip 0xdb1b8) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x128a7d [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128a7d) (movR32Imm32Effect 0x128a7d 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x128a7d 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x128a7d 0xba (by decide) 0x1) pre_rip
  have f4 : InstrSpec 0x128a82 [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x128a82) (movR64R64Effect 0x128a82 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x128a82 14 7).toInstrSpec (mov_r64_r64_effect_step 0x128a82 0x49 0xfe (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x128a85 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x128a85) (movR64R64Effect 0x128a85 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128a85 7 0).toInstrSpec (mov_r64_r64_effect_step 0x128a85 0x48 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128a72) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128a76) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128a7d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128a82) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128a85) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (3, 3)]) (p' := 0x128a88) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128a6f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a6f :=
  Rest.liftedBlock (rest_l128a6f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a6f x hx)

theorem rest_l128a8b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a8b bytes_l128a8b) (entryMap (live .l128a8b))
      5 0x128a8b bytes_l128a8b b_l128a8b := by
  have f0 : InstrSpec 0x128a8b [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x128a8b) (movR64R64Effect 0x128a8b 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128a8b 7 14).toInstrSpec (mov_r64_r64_effect_step 0x128a8b 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128a8e [0x89, 0xC1] (fun s => s.RIP = 0x128a8e) (movR32R32Effect 0x128a8e 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x128a8e 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x128a8e 0xc1 (by decide)) pre_rip
  have f2 : InstrSpec 0x128a90 [0xB0, 0x01] (fun s => s.RIP = 0x128a90) (movR8Imm8Effect 0x128a90 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x128a90 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x128a90 0xb0 (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x128a92 [0x84, 0xC9] (fun s => s.RIP = 0x128a92) (testR8R8Effect 0x128a92 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128a92 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x128a92 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a8e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a90) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a92) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a94) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x128a94 5 0x1f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128a8b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a8b :=
  Rest.liftedBlock (rest_l128a8b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a8b x hx)

theorem rest_l128a96 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a96 bytes_l128a96) (entryMap (live .l128a96))
      6 0x128a96 bytes_l128a96 b_l128a96 := by
  have f0 : InstrSpec 0x128a96 [0x48, 0x8B, 0x03] (LoadPre 0x128a96 (fun s => AddrMode.addr (.base 3 .none) s (0x128a96 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128a96 0 (.base 3 .none))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128a96 0 (.base 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128a96 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128a99 [0x48, 0x8B, 0x4B, 0x08] (LoadPre 0x128a99 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x128a99 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128a99 1 (.base 3 (.d8 0x8)))
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x128a99 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x128a99 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128a9d [0x48, 0x8D, 0x35, 0x90, 0xB1, 0x0D, 0x00] (fun s => s.RIP = 0x128a9d) (leaR64Effect 0x128a9d 6 (.rip 0xdb190))
      [] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x128a9d 6 (.rip 0xdb190)).toInstrSpec (lea_r64_effect_step 0x128a9d 0x48 (by decide) 6 (.rip 0xdb190) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x128aa4 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128aa4) (movR32Imm32Effect 0x128aa4 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x128aa4 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x128aa4 0xba (by decide) 0x1) pre_rip
  have f4 : InstrSpec 0x128aa9 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x128aa9) (movR64R64Effect 0x128aa9 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x128aa9 3 7).toInstrSpec (mov_r64_r64_effect_step 0x128aa9 0x48 0xfb (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x128aac [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x128aac) (movR64R64Effect 0x128aac 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128aac 7 0).toInstrSpec (mov_r64_r64_effect_step 0x128aac 0x48 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128a99) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128a9d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128aa4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128aa9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (7, 7)]) (p' := 0x128aac) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53)]) (p' := 0x128aaf) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128a96 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a96 :=
  Rest.liftedBlock (rest_l128a96 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a96 x hx)

theorem rest_l128ab2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128ab2 bytes_l128ab2) (entryMap (live .l128ab2))
      1 0x128ab2 bytes_l128ab2 b_l128ab2 := by
  have f0 : InstrSpec 0x128ab2 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x128ab2) (movR64R64Effect 0x128ab2 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128ab2 7 3).toInstrSpec (mov_r64_r64_effect_step 0x128ab2 0x48 0xdf (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ab5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l128ab2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128ab2 :=
  Rest.liftedBlock (rest_l128ab2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128ab2 x hx)

theorem rest_l128ab5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128ab5 bytes_l128ab5) (entryMap (live .l128ab5))
      3 0x128ab5 bytes_l128ab5 b_l128ab5 := by
  have f0 : InstrSpec 0x128ab5 [0x5B] (PopPre 0x128ab5) (popR64Effect 0x128ab5 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128ab5 1 3).toInstrSpec (pop_r64_effect_step 0x128ab5 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x128ab6 [0x41, 0x5E] (PopPre 0x128ab6) (popR64Effect 0x128ab6 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128ab6 2 14).toInstrSpec (pop_r64_rex_effect_step 0x128ab6 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x128ab8 [0x5D] (PopPre 0x128ab8) (popR64Effect 0x128ab8 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128ab8 1 5).toInstrSpec (pop_r64_effect_step 0x128ab8 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 53), (4, 54), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ab6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 57) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (3, 53), (4, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ab8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 2), (3, 53), (4, 60), (5, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ab9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 62) (by decide) rfl

theorem block_l128ab5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128ab5 :=
  Rest.liftedBlock (rest_l128ab5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128ab5 x hx)

theorem rest_l128ab9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128ab9 bytes_l128ab9) (entryMap (live .l128ab9))
      2 0x128ab9 bytes_l128ab9 b_l128ab9 := by
  have f0 : InstrSpec 0x128ab9 [0x88, 0x47, 0x10] (StorePre 0x128ab9 3 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x128ab9 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x128ab9 3 0 (.base 7 (.d8 0x10)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x128ab9 3 0 (.base 7 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x128ab9 0 (by decide) (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x128abc [0x89, 0xC1] (fun s => s.RIP = 0x128abc) (movR32R32Effect 0x128abc 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x128abc 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x128abc 0xc1 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128abc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128abe) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 56) (by decide) rfl

theorem block_l128ab9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128ab9 :=
  Rest.liftedBlock (rest_l128ab9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128ab9 x hx)

theorem rest_l128abe [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128abe bytes_l128abe) (entryMap (live .l128abe))
      2 0x128abe bytes_l128abe b_l128abe := by
  have f0 : InstrSpec 0x128abe [0x89, 0xC8] (fun s => s.RIP = 0x128abe) (movR32R32Effect 0x128abe 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x128abe 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x128abe 0xc8 (by decide)) pre_rip
  have f1 : InstrSpec 0x128ac0 [0xC3] (RetPre 0x128ac0) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x128ac0).toInstrSpec (ret_effect_step 0x128ac0) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ac0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 57) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f1 (by decide) rfl rfl rfl (by decide)

theorem block_l128abe [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128abe :=
  Rest.liftedBlock (rest_l128abe code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128abe x hx)

theorem rest_l128ad0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128ad0 bytes_l128ad0) (entryMap (live .l128ad0))
      13 0x128ad0 bytes_l128ad0 b_l128ad0 := by
  have f0 : InstrSpec 0x128ad0 [0x55] (PushPre 0x128ad0 1) (pushR64Effect 0x128ad0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128ad0 1 5).toInstrSpec (push_r64_effect_step 0x128ad0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x128ad1 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x128ad1) (movR64R64Effect 0x128ad1 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x128ad1 5 4).toInstrSpec (mov_r64_r64_effect_step 0x128ad1 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128ad4 [0x41, 0x57] (PushPre 0x128ad4 2) (pushR64Effect 0x128ad4 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128ad4 2 15).toInstrSpec (push_r64_rex_effect_step 0x128ad4 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x128ad6 [0x41, 0x56] (PushPre 0x128ad6 2) (pushR64Effect 0x128ad6 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128ad6 2 14).toInstrSpec (push_r64_rex_effect_step 0x128ad6 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x128ad8 [0x53] (PushPre 0x128ad8 1) (pushR64Effect 0x128ad8 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128ad8 1 3).toInstrSpec (push_r64_effect_step 0x128ad8 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x128ad9 [0x50] (PushPre 0x128ad9 1) (pushR64Effect 0x128ad9 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128ad9 1 0).toInstrSpec (push_r64_effect_step 0x128ad9 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x128ada [0x48, 0x89, 0xCB] (fun s => s.RIP = 0x128ada) (movR64R64Effect 0x128ada 3 1)
      [.gpr 1] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x128ada 3 1).toInstrSpec (mov_r64_r64_effect_step 0x128ada 0x48 0xcb (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x128add [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x128add) (movR64R64Effect 0x128add 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x128add 14 6).toInstrSpec (mov_r64_r64_effect_step 0x128add 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x128ae0 [0x49, 0x89, 0xFF] (fun s => s.RIP = 0x128ae0) (movR64R64Effect 0x128ae0 15 7)
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x128ae0 15 7).toInstrSpec (mov_r64_r64_effect_step 0x128ae0 0x49 0xff (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x128ae3 [0x48, 0x8B, 0x3E] (LoadPre 0x128ae3 (fun s => AddrMode.addr (.base 6 .none) s (0x128ae3 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128ae3 7 (.base 6 .none))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x128ae3 7 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128ae3 0x48 (by decide) 7 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x128ae6 [0x48, 0x8B, 0x46, 0x08] (LoadPre 0x128ae6 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x128ae6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128ae6 0 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128ae6 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x128ae6 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x128aea [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x128aea) (movR64R64Effect 0x128aea 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x128aea 6 2).toInstrSpec (mov_r64_r64_effect_step 0x128aea 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x128aed [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x128aed) (movR64R64Effect 0x128aed 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x128aed 2 1).toInstrSpec (mov_r64_r64_effect_step 0x128aed 0x48 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x128ad1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x128ad4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x128ad6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 58), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x128ad8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 60), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x128ad9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x128ada) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x128add) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (6, 6), (7, 7), (15, 15)]) (p' := 0x128ae0) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (6, 6), (7, 7)]) (p' := 0x128ae3) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (6, 6)]) (p' := 0x128ae6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(1, 1), (2, 2), (6, 6)]) (p' := 0x128aea) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2)]) (p' := 0x128aed) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(1, 1)]) (p' := 0x128af0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128ad0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128ad0 :=
  Rest.liftedBlock (rest_l128ad0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128ad0 x hx)

theorem rest_l128af3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128af3 bytes_l128af3) (entryMap (live .l128af3))
      12 0x128af3 bytes_l128af3 b_l128af3 := by
  have f0 : InstrSpec 0x128af3 [0x48, 0x85, 0xDB] (fun s => s.RIP = 0x128af3) (testR64R64Effect 0x128af3 3 3)
      [.gpr 3, .gpr 3] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x128af3 3 3).toInstrSpec (test_r64_r64_effect_step 0x128af3 0x48 0xdb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128af6 [0x4D, 0x89, 0x77, 0x08] (StorePre 0x128af6 4 (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x128af6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128af6 14 (.base 15 (.d8 0x8)))
      [.gpr 14, .gpr 15] [] [.rip] :=
    (movM64R64Effect_footprint 0x128af6 14 (.base 15 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x128af6 0x4d (by decide) 6 (.base 15 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x128afa [0x41, 0x88, 0x47, 0x10] (StorePre 0x128afa 4 (fun s => AddrMode.addr (.base 15 (.d8 0x10)) s (0x128afa + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x128afa 4 0 (.base 15 (.d8 0x10)))
      [.gpr 0, .gpr 15] [] [.rip] :=
    (movM8R8Effect_footprint 0x128afa 4 0 (.base 15 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x128afa 0x41 (by decide) 0 (.base 15 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x128afe [0x49, 0xC7, 0x07, 0x00, 0x00, 0x00, 0x00] (StorePre 0x128afe 7 (fun s => AddrMode.addr (.base 15 .none) s (0x128afe + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x128afe (.base 15 .none) 0x0)
      [.gpr 15] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x128afe (.base 15 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x128afe 0x49 (by decide) (.base 15 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x128b05 [0x41, 0x0F, 0x94, 0x47, 0x11] (StorePre 0x128b05 5 (fun s => AddrMode.addr (.base 15 (.d8 0x11)) s (0x128b05 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x128b05 5 (.base 15 (.d8 0x11))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 15] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x128b05 5 (.base 15 (.d8 0x11)) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_rex_effect_step 0x128b05 4 0x41 (by decide) 0 (.base 15 (.d8 0x11)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x128b0a [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x128b0a) (movR64R64Effect 0x128b0a 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x128b0a 0 15).toInstrSpec (mov_r64_r64_effect_step 0x128b0a 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x128b0d [0x48, 0x83, 0xC4, 0x08] (fun s => s.RIP = 0x128b0d) (addR64Imm8Effect 0x128b0d 4 0x8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x128b0d 4 0x8).toInstrSpec (add_r64_imm8_effect_step 0x128b0d 0x48 0xc4 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x128b11 [0x5B] (PopPre 0x128b11) (popR64Effect 0x128b11 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128b11 1 3).toInstrSpec (pop_r64_effect_step 0x128b11 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x128b12 [0x41, 0x5E] (PopPre 0x128b12) (popR64Effect 0x128b12 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128b12 2 14).toInstrSpec (pop_r64_rex_effect_step 0x128b12 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x128b14 [0x41, 0x5F] (PopPre 0x128b14) (popR64Effect 0x128b14 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128b14 2 15).toInstrSpec (pop_r64_rex_effect_step 0x128b14 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x128b16 [0x5D] (PopPre 0x128b16) (popR64Effect 0x128b16 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128b16 1 5).toInstrSpec (pop_r64_effect_step 0x128b16 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x128b17 [0xC3] (RetPre 0x128b17) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x128b17).toInstrSpec (ret_effect_step 0x128b17) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128af6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128afa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128afe) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b05) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b0a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b0d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b11) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 63), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b12) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 63), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 66), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b14) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 63), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b16) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 63), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b17) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 63), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f11 (by decide) rfl rfl rfl (by decide)

theorem block_l128af3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128af3 :=
  Rest.liftedBlock (rest_l128af3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128af3 x hx)

theorem rest_l129560 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129560 bytes_l129560) (entryMap (live .l129560))
      12 0x129560 bytes_l129560 b_l129560 := by
  have f0 : InstrSpec 0x129560 [0x55] (PushPre 0x129560 1) (pushR64Effect 0x129560 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129560 1 5).toInstrSpec (push_r64_effect_step 0x129560 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129561 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129561) (movR64R64Effect 0x129561 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129561 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129561 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129564 [0x48, 0x83, 0xEC, 0x20] (fun s => s.RIP = 0x129564) (subR64Imm8Effect 0x129564 4 0x20)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x129564 4 0x20).toInstrSpec (sub_r64_imm8_effect_step 0x129564 0x48 0xec 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129568 [0x48, 0x89, 0x7D, 0xF0] (StorePre 0x129568 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x129568 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129568 7 (.base 5 (.d8 0xf0)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129568 7 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x129568 0x48 (by decide) 7 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12956c [0x48, 0x89, 0x75, 0xF8] (StorePre 0x12956c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x12956c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12956c 6 (.base 5 (.d8 0xf8)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12956c 6 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x12956c 0x48 (by decide) 6 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x129570 [0x48, 0x8D, 0x45, 0xF0] (fun s => s.RIP = 0x129570) (leaR64Effect 0x129570 0 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129570 0 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x129570 0x48 (by decide) 0 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129574 [0x48, 0x89, 0x45, 0xE0] (StorePre 0x129574 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x129574 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129574 0 (.base 5 (.d8 0xe0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129574 0 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x129574 0x48 (by decide) 0 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x129578 [0x48, 0x8D, 0x05, 0xF1, 0x0A, 0x00, 0x00] (fun s => s.RIP = 0x129578) (leaR64Effect 0x129578 0 (.rip 0xaf1))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129578 0 (.rip 0xaf1)).toInstrSpec (lea_r64_effect_step 0x129578 0x48 (by decide) 0 (.rip 0xaf1) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12957f [0x48, 0x89, 0x45, 0xE8] (StorePre 0x12957f 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x12957f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12957f 0 (.base 5 (.d8 0xe8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12957f 0 (.base 5 (.d8 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x12957f 0x48 (by decide) 0 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x129583 [0x48, 0x8D, 0x3D, 0x81, 0x84, 0x0D, 0x00] (fun s => s.RIP = 0x129583) (leaR64Effect 0x129583 7 (.rip 0xd8481))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x129583 7 (.rip 0xd8481)).toInstrSpec (lea_r64_effect_step 0x129583 0x48 (by decide) 7 (.rip 0xd8481) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x12958a [0x48, 0x8D, 0x75, 0xE0] (fun s => s.RIP = 0x12958a) (leaR64Effect 0x12958a 6 (.base 5 (.d8 0xe0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x12958a 6 (.base 5 (.d8 0xe0))).toInstrSpec (lea_r64_effect_step 0x12958a 0x48 (by decide) 6 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12958e [0xFF, 0x15, 0x4C, 0xA8, 0x0D, 0x00] (GoesTo (CallMemPre 0x12958e (.rip 0xda84c)) (callEffect (callMemPtr 0x12958e (.rip 0xda84c)) (0x12958e + BitVec.ofNat 64 (callMemLen (.rip 0xda84c)))) 0x129770) (callEffect (callMemPtr 0x12958e (.rip 0xda84c)) (0x12958e + BitVec.ofNat 64 (callMemLen (.rip 0xda84c))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x12958e (.rip 0xda84c)).toInstrSpec (call_m64_effect_step 0x12958e (.rip 0xda84c) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 53), (5, 5), (6, 6), (7, 7)]) (p' := 0x129561) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 53), (5, 55), (6, 6), (7, 7)]) (p' := 0x129564) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129568) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x12956c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129570) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129574) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129578) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x12957f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129583) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 64), (2, 2), (4, 57), (5, 55), (6, 6), (7, 67)]) (p' := 0x12958a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 64), (2, 2), (4, 57), (5, 55), (6, 69), (7, 67)]) (p' := 0x12958e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 64), (2, 2), (4, 71), (5, 55), (6, 69), (7, 67)]) (p' := 0x129770) f11 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l129560 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129560 :=
  Rest.liftedBlock (rest_l129560 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129560 x hx)

theorem rest_l129594 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129594 bytes_l129594) (entryMap (live .l129594))
      2 0x129594 bytes_l129594 b_l129594 := by
  have f0 : InstrSpec 0x129594 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129594) (fun _ => nopEffect 0x129594 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x129594 10).toInstrSpec (nop_m_effect_step 0x129594 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12959e [0x66, 0x90] (fun s => s.RIP = 0x12959e) (fun _ => nopEffect 0x12959e 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12959e 2).toInstrSpec (nop_66_effect_step 0x12959e) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8)]) (p' := 0x12959e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8)]) (p' := 0x1295a0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l129594 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129594 :=
  Rest.liftedBlock (rest_l129594 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129594 x hx)

theorem rest_l1295a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1295a0 bytes_l1295a0) (entryMap (live .l1295a0))
      19 0x1295a0 bytes_l1295a0 b_l1295a0 := by
  have f0 : InstrSpec 0x1295a0 [0x55] (PushPre 0x1295a0 1) (pushR64Effect 0x1295a0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1295a0 1 5).toInstrSpec (push_r64_effect_step 0x1295a0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1295a1 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x1295a1) (movR64R64Effect 0x1295a1 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x1295a1 5 4).toInstrSpec (mov_r64_r64_effect_step 0x1295a1 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1295a4 [0x48, 0x83, 0xEC, 0x40] (fun s => s.RIP = 0x1295a4) (subR64Imm8Effect 0x1295a4 4 0x40)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1295a4 4 0x40).toInstrSpec (sub_r64_imm8_effect_step 0x1295a4 0x48 0xec 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1295a8 [0x48, 0x89, 0x7D, 0xF0] (StorePre 0x1295a8 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x1295a8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1295a8 7 (.base 5 (.d8 0xf0)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1295a8 7 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x1295a8 0x48 (by decide) 7 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1295ac [0x48, 0x89, 0x75, 0xF8] (StorePre 0x1295ac 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x1295ac + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1295ac 6 (.base 5 (.d8 0xf8)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1295ac 6 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x1295ac 0x48 (by decide) 6 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1295b0 [0x48, 0x89, 0x55, 0xE0] (StorePre 0x1295b0 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x1295b0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1295b0 2 (.base 5 (.d8 0xe0)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1295b0 2 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x1295b0 0x48 (by decide) 2 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1295b4 [0x48, 0x89, 0x4D, 0xE8] (StorePre 0x1295b4 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x1295b4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1295b4 1 (.base 5 (.d8 0xe8)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1295b4 1 (.base 5 (.d8 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x1295b4 0x48 (by decide) 1 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1295b8 [0x48, 0x8D, 0x45, 0xF0] (fun s => s.RIP = 0x1295b8) (leaR64Effect 0x1295b8 0 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1295b8 0 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x1295b8 0x48 (by decide) 0 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1295bc [0x48, 0x89, 0x45, 0xC0] (StorePre 0x1295bc 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x1295bc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1295bc 0 (.base 5 (.d8 0xc0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1295bc 0 (.base 5 (.d8 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x1295bc 0x48 (by decide) 0 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1295c0 [0x48, 0x8D, 0x05, 0xA9, 0x0A, 0x00, 0x00] (fun s => s.RIP = 0x1295c0) (leaR64Effect 0x1295c0 0 (.rip 0xaa9))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1295c0 0 (.rip 0xaa9)).toInstrSpec (lea_r64_effect_step 0x1295c0 0x48 (by decide) 0 (.rip 0xaa9) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1295c7 [0x48, 0x89, 0x45, 0xC8] (StorePre 0x1295c7 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x1295c7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1295c7 0 (.base 5 (.d8 0xc8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1295c7 0 (.base 5 (.d8 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x1295c7 0x48 (by decide) 0 (.base 5 (.d8 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1295cb [0x48, 0x8D, 0x45, 0xE0] (fun s => s.RIP = 0x1295cb) (leaR64Effect 0x1295cb 0 (.base 5 (.d8 0xe0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1295cb 0 (.base 5 (.d8 0xe0))).toInstrSpec (lea_r64_effect_step 0x1295cb 0x48 (by decide) 0 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1295cf [0x48, 0x89, 0x45, 0xD0] (StorePre 0x1295cf 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x1295cf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1295cf 0 (.base 5 (.d8 0xd0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1295cf 0 (.base 5 (.d8 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x1295cf 0x48 (by decide) 0 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1295d3 [0x48, 0x8D, 0x05, 0x76, 0x0A, 0x00, 0x00] (fun s => s.RIP = 0x1295d3) (leaR64Effect 0x1295d3 0 (.rip 0xa76))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1295d3 0 (.rip 0xa76)).toInstrSpec (lea_r64_effect_step 0x1295d3 0x48 (by decide) 0 (.rip 0xa76) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1295da [0x48, 0x89, 0x45, 0xD8] (StorePre 0x1295da 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x1295da + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1295da 0 (.base 5 (.d8 0xd8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1295da 0 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x1295da 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1295de [0x48, 0x8D, 0x3D, 0x22, 0x84, 0x0D, 0x00] (fun s => s.RIP = 0x1295de) (leaR64Effect 0x1295de 7 (.rip 0xd8422))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1295de 7 (.rip 0xd8422)).toInstrSpec (lea_r64_effect_step 0x1295de 0x48 (by decide) 7 (.rip 0xd8422) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1295e5 [0x48, 0x8D, 0x75, 0xC0] (fun s => s.RIP = 0x1295e5) (leaR64Effect 0x1295e5 6 (.base 5 (.d8 0xc0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1295e5 6 (.base 5 (.d8 0xc0))).toInstrSpec (lea_r64_effect_step 0x1295e5 0x48 (by decide) 6 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1295e9 [0x4C, 0x89, 0xC2] (fun s => s.RIP = 0x1295e9) (movR64R64Effect 0x1295e9 2 8)
      [.gpr 8] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1295e9 2 8).toInstrSpec (mov_r64_r64_effect_step 0x1295e9 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1295ec [0xFF, 0x15, 0xEE, 0xA7, 0x0D, 0x00] (GoesTo (CallMemPre 0x1295ec (.rip 0xda7ee)) (callEffect (callMemPtr 0x1295ec (.rip 0xda7ee)) (0x1295ec + BitVec.ofNat 64 (callMemLen (.rip 0xda7ee)))) 0x129770) (callEffect (callMemPtr 0x1295ec (.rip 0xda7ee)) (0x1295ec + BitVec.ofNat 64 (callMemLen (.rip 0xda7ee))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1295ec (.rip 0xda7ee)).toInstrSpec (call_m64_effect_step 0x1295ec (.rip 0xda7ee) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8)]) (p' := 0x1295a1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (4, 53), (5, 55), (6, 6), (7, 7), (8, 8)]) (p' := 0x1295a4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8)]) (p' := 0x1295a8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8)]) (p' := 0x1295ac) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8)]) (p' := 0x1295b0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8)]) (p' := 0x1295b4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8)]) (p' := 0x1295b8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8)]) (p' := 0x1295bc) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8)]) (p' := 0x1295c0) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8)]) (p' := 0x1295c7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8)]) (p' := 0x1295cb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8)]) (p' := 0x1295cf) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8)]) (p' := 0x1295d3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8)]) (p' := 0x1295da) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8)]) (p' := 0x1295de) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 72), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 75), (8, 8)]) (p' := 0x1295e5) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 72), (1, 1), (2, 2), (4, 57), (5, 55), (6, 77), (7, 75), (8, 8)]) (p' := 0x1295e9) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 72), (1, 1), (2, 79), (4, 57), (5, 55), (6, 77), (7, 75), (8, 8)]) (p' := 0x1295ec) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 72), (1, 1), (2, 79), (4, 81), (5, 55), (6, 77), (7, 75), (8, 8)]) (p' := 0x129770) f18 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 83) (by decide) (by decide) rfl rfl

theorem block_l1295a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1295a0 :=
  Rest.liftedBlock (rest_l1295a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1295a0 x hx)

theorem rest_l1295f2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1295f2 bytes_l1295f2) (entryMap (live .l1295f2))
      15 0x1295f2 bytes_l1295f2 b_l1295f2 := by
  have f0 : InstrSpec 0x1295f2 [0x55] (PushPre 0x1295f2 1) (pushR64Effect 0x1295f2 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1295f2 1 5).toInstrSpec (push_r64_effect_step 0x1295f2 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1295f3 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x1295f3) (movR64R64Effect 0x1295f3 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x1295f3 5 4).toInstrSpec (mov_r64_r64_effect_step 0x1295f3 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1295f6 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x1295f6) (subR64Imm8Effect 0x1295f6 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1295f6 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x1295f6 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1295fa [0x48, 0x8D, 0x45, 0xF8] (fun s => s.RIP = 0x1295fa) (leaR64Effect 0x1295fa 0 (.base 5 (.d8 0xf8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1295fa 0 (.base 5 (.d8 0xf8))).toInstrSpec (lea_r64_effect_step 0x1295fa 0x48 (by decide) 0 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1295fe [0x48, 0x89, 0x38] (StorePre 0x1295fe 3 (fun s => AddrMode.addr (.base 0 .none) s (0x1295fe + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1295fe 7 (.base 0 .none))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x1295fe 7 (.base 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1295fe 0x48 (by decide) 7 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x129601 [0x48, 0x8D, 0x4D, 0xF0] (fun s => s.RIP = 0x129601) (leaR64Effect 0x129601 1 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x129601 1 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x129601 0x48 (by decide) 1 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129605 [0x48, 0x89, 0x31] (StorePre 0x129605 3 (fun s => AddrMode.addr (.base 1 .none) s (0x129605 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x129605 6 (.base 1 .none))
      [.gpr 6, .gpr 1] [] [.rip] :=
    (movM64R64Effect_footprint 0x129605 6 (.base 1 .none)).toInstrSpec (mov_m64_r64_effect_step 0x129605 0x48 (by decide) 6 (.base 1 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x129608 [0x48, 0x8D, 0x75, 0xD0] (fun s => s.RIP = 0x129608) (leaR64Effect 0x129608 6 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x129608 6 (.base 5 (.d8 0xd0))).toInstrSpec (lea_r64_effect_step 0x129608 0x48 (by decide) 6 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12960c [0x48, 0x89, 0x0E] (StorePre 0x12960c 3 (fun s => AddrMode.addr (.base 6 .none) s (0x12960c + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x12960c 1 (.base 6 .none))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x12960c 1 (.base 6 .none)).toInstrSpec (mov_m64_r64_effect_step 0x12960c 0x48 (by decide) 1 (.base 6 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12960f [0x48, 0x8D, 0x0D, 0x1A, 0x0E, 0x00, 0x00] (fun s => s.RIP = 0x12960f) (leaR64Effect 0x12960f 1 (.rip 0xe1a))
      [] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x12960f 1 (.rip 0xe1a)).toInstrSpec (lea_r64_effect_step 0x12960f 0x48 (by decide) 1 (.rip 0xe1a) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129616 [0x48, 0x89, 0x4E, 0x08] (StorePre 0x129616 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x129616 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129616 1 (.base 6 (.d8 0x8)))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x129616 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x129616 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x12961a [0x48, 0x89, 0x46, 0x10] (StorePre 0x12961a 4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x12961a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12961a 0 (.base 6 (.d8 0x10)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x12961a 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x12961a 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x12961e [0x48, 0x89, 0x4E, 0x18] (StorePre 0x12961e 4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x12961e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12961e 1 (.base 6 (.d8 0x18)))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x12961e 1 (.base 6 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x12961e 0x48 (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x129622 [0x48, 0x8D, 0x3D, 0x32, 0x84, 0x0D, 0x00] (fun s => s.RIP = 0x129622) (leaR64Effect 0x129622 7 (.rip 0xd8432))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x129622 7 (.rip 0xd8432)).toInstrSpec (lea_r64_effect_step 0x129622 0x48 (by decide) 7 (.rip 0xd8432) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x129629 [0xFF, 0x15, 0xB1, 0xA7, 0x0D, 0x00] (GoesTo (CallMemPre 0x129629 (.rip 0xda7b1)) (callEffect (callMemPtr 0x129629 (.rip 0xda7b1)) (0x129629 + BitVec.ofNat 64 (callMemLen (.rip 0xda7b1)))) 0x129770) (callEffect (callMemPtr 0x129629 (.rip 0xda7b1)) (0x129629 + BitVec.ofNat 64 (callMemLen (.rip 0xda7b1))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x129629 (.rip 0xda7b1)).toInstrSpec (call_m64_effect_step 0x129629 (.rip 0xda7b1) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 53), (5, 5), (6, 6), (7, 7)]) (p' := 0x1295f3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 53), (5, 55), (6, 6), (7, 7)]) (p' := 0x1295f6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x1295fa) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x1295fe) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129601) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 62), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129605) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 62), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129608) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 62), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x12960c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 59), (1, 62), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x12960f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x129616) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x12961a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x12961e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x129622) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 57), (5, 55), (6, 65), (7, 73)]) (p' := 0x129629) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 75), (5, 55), (6, 65), (7, 73)]) (p' := 0x129770) f14 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l1295f2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1295f2 :=
  Rest.liftedBlock (rest_l1295f2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1295f2 x hx)

theorem rest_l12962f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12962f bytes_l12962f) (entryMap (live .l12962f))
      1 0x12962f bytes_l12962f b_l12962f := by
  have f0 : InstrSpec 0x12962f [0x90] (fun s => s.RIP = 0x12962f) (fun _ => nopEffect 0x12962f 1)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12962f 1).toInstrSpec (nop_effect_step 0x12962f) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x129630) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l12962f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12962f :=
  Rest.liftedBlock (rest_l12962f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12962f x hx)

theorem rest_l129630 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129630 bytes_l129630) (entryMap (live .l129630))
      12 0x129630 bytes_l129630 b_l129630 := by
  have f0 : InstrSpec 0x129630 [0x55] (PushPre 0x129630 1) (pushR64Effect 0x129630 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129630 1 5).toInstrSpec (push_r64_effect_step 0x129630 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129631 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129631) (movR64R64Effect 0x129631 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129631 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129631 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129634 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x129634) (subR64Imm8Effect 0x129634 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x129634 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x129634 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129638 [0x48, 0x89, 0x7D, 0xD8] (StorePre 0x129638 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x129638 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129638 7 (.base 5 (.d8 0xd8)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129638 7 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x129638 0x48 (by decide) 7 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12963c [0x48, 0x89, 0x75, 0xE0] (StorePre 0x12963c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x12963c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12963c 6 (.base 5 (.d8 0xe0)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12963c 6 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x12963c 0x48 (by decide) 6 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x129640 [0x48, 0x8D, 0x45, 0xD8] (fun s => s.RIP = 0x129640) (leaR64Effect 0x129640 0 (.base 5 (.d8 0xd8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129640 0 (.base 5 (.d8 0xd8))).toInstrSpec (lea_r64_effect_step 0x129640 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129644 [0x48, 0x89, 0x45, 0xE8] (StorePre 0x129644 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x129644 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129644 0 (.base 5 (.d8 0xe8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129644 0 (.base 5 (.d8 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x129644 0x48 (by decide) 0 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x129648 [0x48, 0x89, 0x4D, 0xF0] (StorePre 0x129648 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x129648 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129648 1 (.base 5 (.d8 0xf0)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129648 1 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x129648 0x48 (by decide) 1 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x12964c [0xC6, 0x45, 0xF8, 0x00] (StorePre 0x12964c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x12964c + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x12964c (.base 5 (.d8 0xf8)) 0x0)
      [.gpr 5] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x12964c (.base 5 (.d8 0xf8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x12964c (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x129650 [0x88, 0x55, 0xF9] (StorePre 0x129650 3 (fun s => AddrMode.addr (.base 5 (.d8 0xf9)) s (0x129650 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x129650 3 2 (.base 5 (.d8 0xf9)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x129650 3 2 (.base 5 (.d8 0xf9))).toInstrSpec (mov_m8_r8_effect_step 0x129650 2 (by decide) (.base 5 (.d8 0xf9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x129653 [0x48, 0x8D, 0x7D, 0xE8] (fun s => s.RIP = 0x129653) (leaR64Effect 0x129653 7 (.base 5 (.d8 0xe8)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x129653 7 (.base 5 (.d8 0xe8))).toInstrSpec (lea_r64_effect_step 0x129653 0x48 (by decide) 7 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x129657 [0xFF, 0x15, 0xC3, 0xA7, 0x0D, 0x00] (GoesTo (CallMemPre 0x129657 (.rip 0xda7c3)) (callEffect (callMemPtr 0x129657 (.rip 0xda7c3)) (0x129657 + BitVec.ofNat 64 (callMemLen (.rip 0xda7c3)))) 0x100a20) (callEffect (callMemPtr 0x129657 (.rip 0xda7c3)) (0x129657 + BitVec.ofNat 64 (callMemLen (.rip 0xda7c3))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x129657 (.rip 0xda7c3)).toInstrSpec (call_m64_effect_step 0x129657 (.rip 0xda7c3) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x100a20
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7)]) (p' := 0x129631) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (4, 53), (5, 55), (6, 6), (7, 7)]) (p' := 0x129634) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129638) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x12963c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129640) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129644) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129648) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x12964c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 61), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129650) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129653) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 61), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6)]) (p' := 0x129657) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 1), (2, 2), (5, 55), (6, 6)]) (p' := 0x100a20) f11 (fun _ h => h.2) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l129630 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129630 :=
  Rest.liftedBlock (rest_l129630 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129630 x hx)

theorem rest_l12965d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12965d bytes_l12965d) (entryMap (live .l12965d))
      19 0x12965d bytes_l12965d b_l12965d := by
  have f0 : InstrSpec 0x12965d [0x55] (PushPre 0x12965d 1) (pushR64Effect 0x12965d 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12965d 1 5).toInstrSpec (push_r64_effect_step 0x12965d 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x12965e [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x12965e) (movR64R64Effect 0x12965e 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x12965e 5 4).toInstrSpec (mov_r64_r64_effect_step 0x12965e 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129661 [0x48, 0x81, 0xEC, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129661) (subR64Imm32Effect 0x129661 4 0x80)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x129661 4 0x80).toInstrSpec (sub_r64_imm32_effect_step 0x129661 0x48 0xec 0x80 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129668 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x129668) (movR64R64Effect 0x129668 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x129668 0 2).toInstrSpec (mov_r64_r64_effect_step 0x129668 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12966b [0x48, 0x8B, 0x55, 0x18] (LoadPre 0x12966b (fun s => AddrMode.addr (.base 5 (.d8 0x18)) s (0x12966b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12966b 2 (.base 5 (.d8 0x18)))
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12966b 2 (.base 5 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x12966b 0x48 (by decide) 2 (.base 5 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x12966f [0x48, 0x89, 0x75, 0xF0] (StorePre 0x12966f 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x12966f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12966f 6 (.base 5 (.d8 0xf0)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12966f 6 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x12966f 0x48 (by decide) 6 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x129673 [0x48, 0x89, 0x45, 0xF8] (StorePre 0x129673 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x129673 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129673 0 (.base 5 (.d8 0xf8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129673 0 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x129673 0x48 (by decide) 0 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x129677 [0x48, 0x89, 0x4D, 0xE0] (StorePre 0x129677 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x129677 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129677 1 (.base 5 (.d8 0xe0)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129677 1 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x129677 0x48 (by decide) 1 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x12967b [0x4C, 0x89, 0x45, 0xE8] (StorePre 0x12967b 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x12967b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12967b 8 (.base 5 (.d8 0xe8)))
      [.gpr 8, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12967b 8 (.base 5 (.d8 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x12967b 0x4c (by decide) 0 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12967f [0x48, 0x8D, 0x05, 0x8A, 0xA6, 0x0D, 0x00] (fun s => s.RIP = 0x12967f) (leaR64Effect 0x12967f 0 (.rip 0xda68a))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x12967f 0 (.rip 0xda68a)).toInstrSpec (lea_r64_effect_step 0x12967f 0x48 (by decide) 0 (.rip 0xda68a) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129686 [0x40, 0x0F, 0xB6, 0xCF] (fun s => s.RIP = 0x129686) (movzxR32R8Effect 0x129686 4 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x129686 4 1 7).toInstrSpec (movzx_r32_r8_rex_effect_step 0x129686 0x40 (by decide) 0xcf (by decide)) pre_rip
  have f11 : InstrSpec 0x12968a [0x48, 0x63, 0x34, 0x88] (LoadPre 0x12968a (fun s => AddrMode.addr (.sib 0 (some 1) 2 .none) s (0x12968a + BitVec.ofNat 64 4)) 4) (movsxdR64M32Effect 0x12968a 4 6 (.sib 0 (some 1) 2 .none))
      [.gpr 0, .gpr 1] [] [.reg 6, .rip] :=
    (movsxdR64M32Effect_footprint 0x12968a 4 6 (.sib 0 (some 1) 2 .none)).toInstrSpec (movsxd_r64_m32_effect_step 0x12968a 0x48 (by decide) 6 (.sib 0 (some 1) 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x12968e [0x48, 0x01, 0xC6] (fun s => s.RIP = 0x12968e) (addR64R64Effect 0x12968e 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12968e 6 0).toInstrSpec (add_r64_r64_effect_step 0x12968e 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x129691 [0x48, 0x8D, 0x05, 0x88, 0xA6, 0x0D, 0x00] (fun s => s.RIP = 0x129691) (leaR64Effect 0x129691 0 (.rip 0xda688))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129691 0 (.rip 0xda688)).toInstrSpec (lea_r64_effect_step 0x129691 0x48 (by decide) 0 (.rip 0xda688) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x129698 [0x48, 0x8B, 0x04, 0xC8] (LoadPre 0x129698 (fun s => AddrMode.addr (.sib 0 (some 1) 3 .none) s (0x129698 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129698 0 (.sib 0 (some 1) 3 .none))
      [.gpr 0, .gpr 1] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x129698 0 (.sib 0 (some 1) 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x129698 0x48 (by decide) 0 (.sib 0 (some 1) 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x12969c [0x48, 0x89, 0x75, 0xD0] (StorePre 0x12969c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x12969c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12969c 6 (.base 5 (.d8 0xd0)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12969c 6 (.base 5 (.d8 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x12969c 0x48 (by decide) 6 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x1296a0 [0x48, 0x89, 0x45, 0xD8] (StorePre 0x1296a0 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x1296a0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296a0 0 (.base 5 (.d8 0xd8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296a0 0 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x1296a0 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x1296a4 [0x4D, 0x85, 0xC9] (fun s => s.RIP = 0x1296a4) (testR64R64Effect 0x1296a4 9 9)
      [.gpr 9, .gpr 9] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1296a4 9 9).toInstrSpec (test_r64_r64_effect_step 0x1296a4 0x4d 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x12965e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (4, 53), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x129661) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x129668) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x12966b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 1), (2, 61), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x12966f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 1), (2, 61), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x129673) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 1), (2, 61), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x129677) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 59), (1, 1), (2, 61), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x12967b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 1), (2, 61), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x12967f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 61), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x129686) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 69), (2, 61), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x12968a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 67), (1, 69), (2, 61), (4, 57), (5, 55), (6, 71), (7, 7), (8, 8), (9, 9)]) (p' := 0x12968e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 67), (1, 69), (2, 61), (4, 57), (5, 55), (6, 73), (7, 7), (8, 8), (9, 9)]) (p' := 0x129691) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 69), (2, 61), (4, 57), (5, 55), (6, 73), (7, 7), (8, 8), (9, 9)]) (p' := 0x129698) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 69), (2, 61), (4, 57), (5, 55), (6, 73), (7, 7), (8, 8), (9, 9)]) (p' := 0x12969c) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (1, 69), (2, 61), (4, 57), (5, 55), (6, 73), (7, 7), (8, 8), (9, 9)]) (p' := 0x1296a0) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 77), (1, 69), (2, 61), (4, 57), (5, 55), (6, 73), (7, 7), (8, 8), (9, 9)]) (p' := 0x1296a4) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f17 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 77), (1, 69), (2, 61), (4, 57), (5, 55), (6, 73), (7, 7), (8, 8), (9, 9), (19, 81)]) (p' := 0x1296a7) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 83) (jcc_rel8_effect_step 0x1296a7 5 0x42) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12965d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12965d :=
  Rest.liftedBlock (rest_l12965d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12965d x hx)

theorem rest_l1296a9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1296a9 bytes_l1296a9) (entryMap (live .l1296a9))
      14 0x1296a9 bytes_l1296a9 b_l1296a9 := by
  have f0 : InstrSpec 0x1296a9 [0x48, 0x8D, 0x45, 0xD0] (fun s => s.RIP = 0x1296a9) (leaR64Effect 0x1296a9 0 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1296a9 0 (.base 5 (.d8 0xd0))).toInstrSpec (lea_r64_effect_step 0x1296a9 0x48 (by decide) 0 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1296ad [0x48, 0x8D, 0x75, 0x80] (fun s => s.RIP = 0x1296ad) (leaR64Effect 0x1296ad 6 (.base 5 (.d8 0x80)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1296ad 6 (.base 5 (.d8 0x80))).toInstrSpec (lea_r64_effect_step 0x1296ad 0x48 (by decide) 6 (.base 5 (.d8 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1296b1 [0x48, 0x89, 0x06] (StorePre 0x1296b1 3 (fun s => AddrMode.addr (.base 6 .none) s (0x1296b1 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1296b1 0 (.base 6 .none))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296b1 0 (.base 6 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1296b1 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1296b4 [0x48, 0x8D, 0x05, 0xB5, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x1296b4) (leaR64Effect 0x1296b4 0 (.rip 0x9b5))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1296b4 0 (.rip 0x9b5)).toInstrSpec (lea_r64_effect_step 0x1296b4 0x48 (by decide) 0 (.rip 0x9b5) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1296bb [0x48, 0x89, 0x46, 0x08] (StorePre 0x1296bb 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1296bb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296bb 0 (.base 6 (.d8 0x8)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296bb 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1296bb 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1296bf [0x48, 0x8D, 0x45, 0xF0] (fun s => s.RIP = 0x1296bf) (leaR64Effect 0x1296bf 0 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1296bf 0 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x1296bf 0x48 (by decide) 0 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1296c3 [0x48, 0x89, 0x46, 0x10] (StorePre 0x1296c3 4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1296c3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296c3 0 (.base 6 (.d8 0x10)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296c3 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1296c3 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1296c7 [0x48, 0x8D, 0x05, 0x82, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x1296c7) (leaR64Effect 0x1296c7 0 (.rip 0x982))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1296c7 0 (.rip 0x982)).toInstrSpec (lea_r64_effect_step 0x1296c7 0x48 (by decide) 0 (.rip 0x982) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1296ce [0x48, 0x89, 0x46, 0x18] (StorePre 0x1296ce 4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1296ce + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296ce 0 (.base 6 (.d8 0x18)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296ce 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1296ce 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1296d2 [0x48, 0x8D, 0x4D, 0xE0] (fun s => s.RIP = 0x1296d2) (leaR64Effect 0x1296d2 1 (.base 5 (.d8 0xe0)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x1296d2 1 (.base 5 (.d8 0xe0))).toInstrSpec (lea_r64_effect_step 0x1296d2 0x48 (by decide) 1 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1296d6 [0x48, 0x89, 0x4E, 0x20] (StorePre 0x1296d6 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1296d6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296d6 1 (.base 6 (.d8 0x20)))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296d6 1 (.base 6 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1296d6 0x48 (by decide) 1 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1296da [0x48, 0x89, 0x46, 0x28] (StorePre 0x1296da 4 (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x1296da + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296da 0 (.base 6 (.d8 0x28)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296da 0 (.base 6 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1296da 0x48 (by decide) 0 (.base 6 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1296de [0x48, 0x8D, 0x3D, 0xAD, 0x83, 0x0D, 0x00] (fun s => s.RIP = 0x1296de) (leaR64Effect 0x1296de 7 (.rip 0xd83ad))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1296de 7 (.rip 0xd83ad)).toInstrSpec (lea_r64_effect_step 0x1296de 0x48 (by decide) 7 (.rip 0xd83ad) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1296e5 [0xFF, 0x15, 0xF5, 0xA6, 0x0D, 0x00] (GoesTo (CallMemPre 0x1296e5 (.rip 0xda6f5)) (callEffect (callMemPtr 0x1296e5 (.rip 0xda6f5)) (0x1296e5 + BitVec.ofNat 64 (callMemLen (.rip 0xda6f5)))) 0x129770) (callEffect (callMemPtr 0x1296e5 (.rip 0xda6f5)) (0x1296e5 + BitVec.ofNat 64 (callMemLen (.rip 0xda6f5))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1296e5 (.rip 0xda6f5)).toInstrSpec (call_m64_effect_step 0x1296e5 (.rip 0xda6f5) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (5, 5)]) (p' := 0x1296ad) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296b1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296b4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296bb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296bf) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296c3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296c7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296ce) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296d2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296d6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296da) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 4), (5, 5), (6, 55)]) (p' := 0x1296de) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 4), (5, 5), (6, 55), (7, 71)]) (p' := 0x1296e5) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 73), (5, 5), (6, 55), (7, 71)]) (p' := 0x129770) f13 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l1296a9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1296a9 :=
  Rest.liftedBlock (rest_l1296a9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1296a9 x hx)

theorem rest_l1296eb_1 [Bindings] (code : CodeMap) :
    Rest (n := 83) code lifted (codeRange 0x1296eb bytes_l1296eb) [(0, 74), (1, 77), (2, 2), (4, 4), (5, 5), (6, 61), (7, 81), (9, 9)]
      1 0x129745 bytes_l1296eb_1 b_l1296eb_1 := by
  have f20 : InstrSpec 0x129745 [0xFF, 0x15, 0x95, 0xA6, 0x0D, 0x00] (GoesTo (CallMemPre 0x129745 (.rip 0xda695)) (callEffect (callMemPtr 0x129745 (.rip 0xda695)) (0x129745 + BitVec.ofNat 64 (callMemLen (.rip 0xda695)))) 0x129770) (callEffect (callMemPtr 0x129745 (.rip 0xda695)) (0x129745 + BitVec.ofNat 64 (callMemLen (.rip 0xda695))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x129745 (.rip 0xda695)).toInstrSpec (call_m64_effect_step 0x129745 (.rip 0xda695) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 74), (1, 77), (2, 2), (4, 83), (5, 5), (6, 61), (7, 81), (9, 9)]) (p' := 0x129770) f20 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem rest_l1296eb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1296eb bytes_l1296eb) (entryMap (live .l1296eb))
      21 0x1296eb bytes_l1296eb b_l1296eb := by
  have f0 : InstrSpec 0x1296eb [0x48, 0x8B, 0x45, 0x10] (LoadPre 0x1296eb (fun s => AddrMode.addr (.base 5 (.d8 0x10)) s (0x1296eb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1296eb 0 (.base 5 (.d8 0x10)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1296eb 0 (.base 5 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1296eb 0x48 (by decide) 0 (.base 5 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1296ef [0x48, 0x8D, 0x4D, 0xC0] (fun s => s.RIP = 0x1296ef) (leaR64Effect 0x1296ef 1 (.base 5 (.d8 0xc0)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x1296ef 1 (.base 5 (.d8 0xc0))).toInstrSpec (lea_r64_effect_step 0x1296ef 0x48 (by decide) 1 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1296f3 [0x4C, 0x89, 0x09] (StorePre 0x1296f3 3 (fun s => AddrMode.addr (.base 1 .none) s (0x1296f3 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1296f3 9 (.base 1 .none))
      [.gpr 9, .gpr 1] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296f3 9 (.base 1 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1296f3 0x4c (by decide) 1 (.base 1 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1296f6 [0x48, 0x89, 0x41, 0x08] (StorePre 0x1296f6 4 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x1296f6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296f6 0 (.base 1 (.d8 0x8)))
      [.gpr 0, .gpr 1] [] [.rip] :=
    (movM64R64Effect_footprint 0x1296f6 0 (.base 1 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1296f6 0x48 (by decide) 0 (.base 1 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1296fa [0x48, 0x8D, 0x45, 0xD0] (fun s => s.RIP = 0x1296fa) (leaR64Effect 0x1296fa 0 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1296fa 0 (.base 5 (.d8 0xd0))).toInstrSpec (lea_r64_effect_step 0x1296fa 0x48 (by decide) 0 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1296fe [0x48, 0x8D, 0x75, 0x80] (fun s => s.RIP = 0x1296fe) (leaR64Effect 0x1296fe 6 (.base 5 (.d8 0x80)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1296fe 6 (.base 5 (.d8 0x80))).toInstrSpec (lea_r64_effect_step 0x1296fe 0x48 (by decide) 6 (.base 5 (.d8 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129702 [0x48, 0x89, 0x06] (StorePre 0x129702 3 (fun s => AddrMode.addr (.base 6 .none) s (0x129702 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x129702 0 (.base 6 .none))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x129702 0 (.base 6 .none)).toInstrSpec (mov_m64_r64_effect_step 0x129702 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x129705 [0x48, 0x8D, 0x05, 0x64, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x129705) (leaR64Effect 0x129705 0 (.rip 0x964))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129705 0 (.rip 0x964)).toInstrSpec (lea_r64_effect_step 0x129705 0x48 (by decide) 0 (.rip 0x964) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12970c [0x48, 0x89, 0x46, 0x08] (StorePre 0x12970c 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x12970c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12970c 0 (.base 6 (.d8 0x8)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x12970c 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x12970c 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x129710 [0x48, 0x89, 0x4E, 0x10] (StorePre 0x129710 4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x129710 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129710 1 (.base 6 (.d8 0x10)))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x129710 1 (.base 6 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x129710 0x48 (by decide) 1 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x129714 [0x48, 0x8D, 0x05, 0xE5, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x129714) (leaR64Effect 0x129714 0 (.rip 0x9e5))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129714 0 (.rip 0x9e5)).toInstrSpec (lea_r64_effect_step 0x129714 0x48 (by decide) 0 (.rip 0x9e5) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12971b [0x48, 0x89, 0x46, 0x18] (StorePre 0x12971b 4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x12971b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12971b 0 (.base 6 (.d8 0x18)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x12971b 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x12971b 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x12971f [0x48, 0x8D, 0x45, 0xF0] (fun s => s.RIP = 0x12971f) (leaR64Effect 0x12971f 0 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x12971f 0 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x12971f 0x48 (by decide) 0 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x129723 [0x48, 0x89, 0x46, 0x20] (StorePre 0x129723 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x129723 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129723 0 (.base 6 (.d8 0x20)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x129723 0 (.base 6 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x129723 0x48 (by decide) 0 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x129727 [0x48, 0x8D, 0x05, 0x22, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x129727) (leaR64Effect 0x129727 0 (.rip 0x922))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129727 0 (.rip 0x922)).toInstrSpec (lea_r64_effect_step 0x129727 0x48 (by decide) 0 (.rip 0x922) (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x12972e [0x48, 0x89, 0x46, 0x28] (StorePre 0x12972e 4 (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x12972e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12972e 0 (.base 6 (.d8 0x28)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x12972e 0 (.base 6 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x12972e 0x48 (by decide) 0 (.base 6 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x129732 [0x48, 0x8D, 0x4D, 0xE0] (fun s => s.RIP = 0x129732) (leaR64Effect 0x129732 1 (.base 5 (.d8 0xe0)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x129732 1 (.base 5 (.d8 0xe0))).toInstrSpec (lea_r64_effect_step 0x129732 0x48 (by decide) 1 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x129736 [0x48, 0x89, 0x4E, 0x30] (StorePre 0x129736 4 (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x129736 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129736 1 (.base 6 (.d8 0x30)))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x129736 1 (.base 6 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x129736 0x48 (by decide) 1 (.base 6 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x12973a [0x48, 0x89, 0x46, 0x38] (StorePre 0x12973a 4 (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x12973a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12973a 0 (.base 6 (.d8 0x38)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x12973a 0 (.base 6 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x12973a 0x48 (by decide) 0 (.base 6 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x12973e [0x48, 0x8D, 0x3D, 0x84, 0x83, 0x0D, 0x00] (fun s => s.RIP = 0x12973e) (leaR64Effect 0x12973e 7 (.rip 0xd8384))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x12973e 7 (.rip 0xd8384)).toInstrSpec (lea_r64_effect_step 0x12973e 0x48 (by decide) 7 (.rip 0xd8384) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (5, 5), (9, 9)]) (p' := 0x1296ef) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (4, 4), (5, 5), (9, 9)]) (p' := 0x1296f3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (2, 2), (4, 4), (5, 5), (9, 9)]) (p' := 0x1296f6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (4, 4), (5, 5), (9, 9)]) (p' := 0x1296fa) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (2, 2), (4, 4), (5, 5), (9, 9)]) (p' := 0x1296fe) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x129702) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x129705) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x12970c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x129710) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x129714) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x12971b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x12971f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x129723) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x129727) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x12972e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 74), (1, 55), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x129732) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 74), (1, 77), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x129736) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 74), (1, 77), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x12973a) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 74), (1, 77), (2, 2), (4, 4), (5, 5), (6, 61), (9, 9)]) (p' := 0x12973e) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f19 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 74), (1, 77), (2, 2), (4, 4), (5, 5), (6, 61), (7, 81), (9, 9)]) (p' := 0x129745) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1296eb_1 code

theorem block_l1296eb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1296eb :=
  Rest.liftedBlock (rest_l1296eb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1296eb x hx)

theorem rest_l12974b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12974b bytes_l12974b) (entryMap (live .l12974b))
      1 0x12974b bytes_l12974b b_l12974b := by
  have f0 : InstrSpec 0x12974b [0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x12974b) (fun _ => nopEffect 0x12974b 5)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12974b 5).toInstrSpec (nop_m_effect_step 0x12974b [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x129750) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l12974b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12974b :=
  Rest.liftedBlock (rest_l12974b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12974b x hx)

theorem rest_l129750 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129750 bytes_l129750) (entryMap (live .l129750))
      4 0x129750 bytes_l129750 b_l129750 := by
  have f0 : InstrSpec 0x129750 [0x55] (PushPre 0x129750 1) (pushR64Effect 0x129750 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129750 1 5).toInstrSpec (push_r64_effect_step 0x129750 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129751 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129751) (movR64R64Effect 0x129751 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129751 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129751 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129754 [0x48, 0x8D, 0x34, 0x75, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129754) (leaR64Effect 0x129754 6 (.abs (some 6) 1 0x1))
      [.gpr 6] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x129754 6 (.abs (some 6) 1 0x1)).toInstrSpec (lea_r64_effect_step 0x129754 0x48 (by decide) 6 (.abs (some 6) 1 0x1) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12975c [0xFF, 0x15, 0x7E, 0xA6, 0x0D, 0x00] (GoesTo (CallMemPre 0x12975c (.rip 0xda67e)) (callEffect (callMemPtr 0x12975c (.rip 0xda67e)) (0x12975c + BitVec.ofNat 64 (callMemLen (.rip 0xda67e)))) 0x129770) (callEffect (callMemPtr 0x12975c (.rip 0xda67e)) (0x12975c + BitVec.ofNat 64 (callMemLen (.rip 0xda67e))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x12975c (.rip 0xda67e)).toInstrSpec (call_m64_effect_step 0x12975c (.rip 0xda67e) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 53), (5, 5), (6, 6), (7, 7)]) (p' := 0x129751) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 53), (5, 55), (6, 6), (7, 7)]) (p' := 0x129754) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 53), (5, 55), (6, 57), (7, 7)]) (p' := 0x12975c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (4, 59), (5, 55), (6, 57), (7, 7)]) (p' := 0x129770) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l129750 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129750 :=
  Rest.liftedBlock (rest_l129750 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129750 x hx)

theorem rest_l129762 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129762 bytes_l129762) (entryMap (live .l129762))
      2 0x129762 bytes_l129762 b_l129762 := by
  have f0 : InstrSpec 0x129762 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129762) (fun _ => nopEffect 0x129762 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x129762 10).toInstrSpec (nop_m_effect_step 0x129762 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12976c [0x0F, 0x1F, 0x40, 0x00] (fun s => s.RIP = 0x12976c) (fun _ => nopEffect 0x12976c 4)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12976c 4).toInstrSpec (nop_m_effect_step 0x12976c [] (by decide) (by decide) (.base 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x12976c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x129770) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l129762 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129762 :=
  Rest.liftedBlock (rest_l129762 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129762 x hx)

theorem rest_l129770 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129770 bytes_l129770) (entryMap (live .l129770))
      11 0x129770 bytes_l129770 b_l129770 := by
  have f0 : InstrSpec 0x129770 [0x55] (PushPre 0x129770 1) (pushR64Effect 0x129770 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129770 1 5).toInstrSpec (push_r64_effect_step 0x129770 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129771 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129771) (movR64R64Effect 0x129771 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129771 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129771 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129774 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x129774) (subR64Imm8Effect 0x129774 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x129774 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x129774 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129778 [0x48, 0x89, 0x7D, 0xF0] (StorePre 0x129778 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x129778 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129778 7 (.base 5 (.d8 0xf0)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129778 7 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x129778 0x48 (by decide) 7 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12977c [0x48, 0x89, 0x75, 0xF8] (StorePre 0x12977c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x12977c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12977c 6 (.base 5 (.d8 0xf8)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12977c 6 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x12977c 0x48 (by decide) 6 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x129780 [0x48, 0x8D, 0x45, 0xF0] (fun s => s.RIP = 0x129780) (leaR64Effect 0x129780 0 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129780 0 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x129780 0x48 (by decide) 0 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129784 [0x48, 0x89, 0x45, 0xD8] (StorePre 0x129784 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x129784 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129784 0 (.base 5 (.d8 0xd8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129784 0 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x129784 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x129788 [0x48, 0x89, 0x55, 0xE0] (StorePre 0x129788 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x129788 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129788 2 (.base 5 (.d8 0xe0)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129788 2 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x129788 0x48 (by decide) 2 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x12978c [0x66, 0xC7, 0x45, 0xE8, 0x01, 0x00] (StorePre 0x12978c 6 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x12978c + BitVec.ofNat 64 6)) 2) (movM16Imm16Effect 0x12978c (.base 5 (.d8 0xe8)) 0x1)
      [.gpr 5] [] [.rip] :=
    (movM16Imm16Effect_footprint 0x12978c (.base 5 (.d8 0xe8)) 0x1).toInstrSpec (mov_m16_imm16_effect_step 0x12978c (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x129792 [0x48, 0x8D, 0x7D, 0xD8] (fun s => s.RIP = 0x129792) (leaR64Effect 0x129792 7 (.base 5 (.d8 0xd8)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x129792 7 (.base 5 (.d8 0xd8))).toInstrSpec (lea_r64_effect_step 0x129792 0x48 (by decide) 7 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129796 [0xFF, 0x15, 0x84, 0xA6, 0x0D, 0x00] (GoesTo (CallMemPre 0x129796 (.rip 0xda684)) (callEffect (callMemPtr 0x129796 (.rip 0xda684)) (0x129796 + BitVec.ofNat 64 (callMemLen (.rip 0xda684)))) 0x100a20) (callEffect (callMemPtr 0x129796 (.rip 0xda684)) (0x129796 + BitVec.ofNat 64 (callMemLen (.rip 0xda684))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x129796 (.rip 0xda684)).toInstrSpec (call_m64_effect_step 0x129796 (.rip 0xda684) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x100a20
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 53), (5, 5), (6, 6), (7, 7)]) (p' := 0x129771) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 53), (5, 55), (6, 6), (7, 7)]) (p' := 0x129774) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129778) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x12977c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129780) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129784) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129788) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x12978c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129792) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6)]) (p' := 0x129796) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 61), (2, 2), (5, 55), (6, 6)]) (p' := 0x100a20) f10 (fun _ h => h.2) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l129770 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129770 :=
  Rest.liftedBlock (rest_l129770 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129770 x hx)

theorem rest_l12979c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12979c bytes_l12979c) (entryMap (live .l12979c))
      1 0x12979c bytes_l12979c b_l12979c := by
  have f0 : InstrSpec 0x12979c [0x0F, 0x1F, 0x40, 0x00] (fun s => s.RIP = 0x12979c) (fun _ => nopEffect 0x12979c 4)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12979c 4).toInstrSpec (nop_m_effect_step 0x12979c [] (by decide) (by decide) (.base 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297a0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l12979c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12979c :=
  Rest.liftedBlock (rest_l12979c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12979c x hx)

theorem rest_l129b60 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129b60 bytes_l129b60) (entryMap (live .l129b60))
      5 0x129b60 bytes_l129b60 b_l129b60 := by
  have f0 : InstrSpec 0x129b60 [0x55] (PushPre 0x129b60 1) (pushR64Effect 0x129b60 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129b60 1 5).toInstrSpec (push_r64_effect_step 0x129b60 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129b61 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129b61) (movR64R64Effect 0x129b61 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129b61 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129b61 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129b64 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x129b64) (subR64Imm8Effect 0x129b64 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x129b64 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x129b64 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129b68 [0x48, 0x39, 0xD7] (fun s => s.RIP = 0x129b68) (cmpR64R64Effect 0x129b68 7 2)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129b68 7 2).toInstrSpec (cmp_r64_r64_effect_step 0x129b68 0x48 0xd7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7)]) (p' := 0x129b61) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (4, 53), (5, 55), (6, 6), (7, 7)]) (p' := 0x129b64) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129b68) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (16, 59), (19, 60)]) (p' := 0x129b6b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel8_effect_step 0x129b6b 6 0x3b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129b60 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129b60 :=
  Rest.liftedBlock (rest_l129b60 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129b60 x hx)

theorem rest_l129b6d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129b6d bytes_l129b6d) (entryMap (live .l129b6d))
      13 0x129b6d bytes_l129b6d b_l129b6d := by
  have f0 : InstrSpec 0x129b6d [0x48, 0x89, 0x7D, 0xF8] (StorePre 0x129b6d 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x129b6d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129b6d 7 (.base 5 (.d8 0xf8)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129b6d 7 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x129b6d 0x48 (by decide) 7 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x129b71 [0x48, 0x89, 0x55, 0xF0] (StorePre 0x129b71 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x129b71 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129b71 2 (.base 5 (.d8 0xf0)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129b71 2 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x129b71 0x48 (by decide) 2 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x129b75 [0x48, 0x8D, 0x45, 0xF8] (fun s => s.RIP = 0x129b75) (leaR64Effect 0x129b75 0 (.base 5 (.d8 0xf8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129b75 0 (.base 5 (.d8 0xf8))).toInstrSpec (lea_r64_effect_step 0x129b75 0x48 (by decide) 0 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129b79 [0x48, 0x89, 0x45, 0xD0] (StorePre 0x129b79 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x129b79 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129b79 0 (.base 5 (.d8 0xd0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129b79 0 (.base 5 (.d8 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x129b79 0x48 (by decide) 0 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x129b7d [0x48, 0x8D, 0x05, 0xAC, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x129b7d) (leaR64Effect 0x129b7d 0 (.rip 0x8ac))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129b7d 0 (.rip 0x8ac)).toInstrSpec (lea_r64_effect_step 0x129b7d 0x48 (by decide) 0 (.rip 0x8ac) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x129b84 [0x48, 0x89, 0x45, 0xD8] (StorePre 0x129b84 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x129b84 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129b84 0 (.base 5 (.d8 0xd8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129b84 0 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x129b84 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x129b88 [0x48, 0x8D, 0x55, 0xF0] (fun s => s.RIP = 0x129b88) (leaR64Effect 0x129b88 2 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x129b88 2 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x129b88 0x48 (by decide) 2 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x129b8c [0x48, 0x89, 0x55, 0xE0] (StorePre 0x129b8c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x129b8c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129b8c 2 (.base 5 (.d8 0xe0)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129b8c 2 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x129b8c 0x48 (by decide) 2 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x129b90 [0x48, 0x89, 0x45, 0xE8] (StorePre 0x129b90 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x129b90 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129b90 0 (.base 5 (.d8 0xe8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129b90 0 (.base 5 (.d8 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x129b90 0x48 (by decide) 0 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x129b94 [0x48, 0x8D, 0x3D, 0x16, 0x80, 0x0D, 0x00] (fun s => s.RIP = 0x129b94) (leaR64Effect 0x129b94 7 (.rip 0xd8016))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x129b94 7 (.rip 0xd8016)).toInstrSpec (lea_r64_effect_step 0x129b94 0x48 (by decide) 7 (.rip 0xd8016) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129b9b [0x48, 0x8D, 0x75, 0xD0] (fun s => s.RIP = 0x129b9b) (leaR64Effect 0x129b9b 6 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x129b9b 6 (.base 5 (.d8 0xd0))).toInstrSpec (lea_r64_effect_step 0x129b9b 0x48 (by decide) 6 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x129b9f [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x129b9f) (movR64R64Effect 0x129b9f 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x129b9f 2 1).toInstrSpec (mov_r64_r64_effect_step 0x129b9f 0x48 0xca (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x129ba2 [0xFF, 0x15, 0x38, 0xA2, 0x0D, 0x00] (GoesTo (CallMemPre 0x129ba2 (.rip 0xda238)) (callEffect (callMemPtr 0x129ba2 (.rip 0xda238)) (0x129ba2 + BitVec.ofNat 64 (callMemLen (.rip 0xda238)))) 0x129770) (callEffect (callMemPtr 0x129ba2 (.rip 0xda238)) (0x129ba2 + BitVec.ofNat 64 (callMemLen (.rip 0xda238))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x129ba2 (.rip 0xda238)).toInstrSpec (call_m64_effect_step 0x129ba2 (.rip 0xda238) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (7, 7)]) (p' := 0x129b71) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (7, 7)]) (p' := 0x129b75) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (7, 7)]) (p' := 0x129b79) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (7, 7)]) (p' := 0x129b7d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (2, 2), (4, 4), (5, 5), (7, 7)]) (p' := 0x129b84) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (1, 1), (2, 2), (4, 4), (5, 5), (7, 7)]) (p' := 0x129b88) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (7, 7)]) (p' := 0x129b8c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (7, 7)]) (p' := 0x129b90) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (7, 7)]) (p' := 0x129b94) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (7, 65)]) (p' := 0x129b9b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 67), (7, 65)]) (p' := 0x129b9f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 58), (1, 1), (2, 69), (4, 4), (5, 5), (6, 67), (7, 65)]) (p' := 0x129ba2) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 58), (1, 1), (2, 69), (4, 71), (5, 5), (6, 67), (7, 65)]) (p' := 0x129770) f12 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l129b6d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129b6d :=
  Rest.liftedBlock (rest_l129b6d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129b6d x hx)

theorem rest_l129ba8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129ba8 bytes_l129ba8) (entryMap (live .l129ba8))
      2 0x129ba8 bytes_l129ba8 b_l129ba8 := by
  have f0 : InstrSpec 0x129ba8 [0x48, 0x39, 0xD6] (fun s => s.RIP = 0x129ba8) (cmpR64R64Effect 0x129ba8 6 2)
      [.gpr 6, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129ba8 6 2).toInstrSpec (cmp_r64_r64_effect_step 0x129ba8 0x48 0xd6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54)]) (p' := 0x129bab) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x129bab 7 0x40) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129ba8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129ba8 :=
  Rest.liftedBlock (rest_l129ba8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129ba8 x hx)

theorem rest_l129bad [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129bad bytes_l129bad) (entryMap (live .l129bad))
      2 0x129bad bytes_l129bad b_l129bad := by
  have f0 : InstrSpec 0x129bad [0x48, 0x39, 0xF7] (fun s => s.RIP = 0x129bad) (cmpR64R64Effect 0x129bad 7 6)
      [.gpr 7, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129bad 7 6).toInstrSpec (cmp_r64_r64_effect_step 0x129bad 0x48 0xf7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54)]) (p' := 0x129bb0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x129bb0 6 0x3b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129bad [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129bad :=
  Rest.liftedBlock (rest_l129bad code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129bad x hx)

theorem rest_l129bb2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129bb2 bytes_l129bb2) (entryMap (live .l129bb2))
      13 0x129bb2 bytes_l129bb2 b_l129bb2 := by
  have f0 : InstrSpec 0x129bb2 [0x48, 0x89, 0x7D, 0xF8] (StorePre 0x129bb2 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x129bb2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129bb2 7 (.base 5 (.d8 0xf8)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129bb2 7 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x129bb2 0x48 (by decide) 7 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x129bb6 [0x48, 0x89, 0x75, 0xF0] (StorePre 0x129bb6 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x129bb6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129bb6 6 (.base 5 (.d8 0xf0)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129bb6 6 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x129bb6 0x48 (by decide) 6 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x129bba [0x48, 0x8D, 0x45, 0xF8] (fun s => s.RIP = 0x129bba) (leaR64Effect 0x129bba 0 (.base 5 (.d8 0xf8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129bba 0 (.base 5 (.d8 0xf8))).toInstrSpec (lea_r64_effect_step 0x129bba 0x48 (by decide) 0 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129bbe [0x48, 0x89, 0x45, 0xD0] (StorePre 0x129bbe 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x129bbe + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129bbe 0 (.base 5 (.d8 0xd0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129bbe 0 (.base 5 (.d8 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x129bbe 0x48 (by decide) 0 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x129bc2 [0x48, 0x8D, 0x05, 0x67, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x129bc2) (leaR64Effect 0x129bc2 0 (.rip 0x867))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129bc2 0 (.rip 0x867)).toInstrSpec (lea_r64_effect_step 0x129bc2 0x48 (by decide) 0 (.rip 0x867) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x129bc9 [0x48, 0x89, 0x45, 0xD8] (StorePre 0x129bc9 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x129bc9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129bc9 0 (.base 5 (.d8 0xd8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129bc9 0 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x129bc9 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x129bcd [0x48, 0x8D, 0x55, 0xF0] (fun s => s.RIP = 0x129bcd) (leaR64Effect 0x129bcd 2 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x129bcd 2 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x129bcd 0x48 (by decide) 2 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x129bd1 [0x48, 0x89, 0x55, 0xE0] (StorePre 0x129bd1 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x129bd1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129bd1 2 (.base 5 (.d8 0xe0)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129bd1 2 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x129bd1 0x48 (by decide) 2 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x129bd5 [0x48, 0x89, 0x45, 0xE8] (StorePre 0x129bd5 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x129bd5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129bd5 0 (.base 5 (.d8 0xe8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129bd5 0 (.base 5 (.d8 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x129bd5 0x48 (by decide) 0 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x129bd9 [0x48, 0x8D, 0x3D, 0xA9, 0x7F, 0x0D, 0x00] (fun s => s.RIP = 0x129bd9) (leaR64Effect 0x129bd9 7 (.rip 0xd7fa9))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x129bd9 7 (.rip 0xd7fa9)).toInstrSpec (lea_r64_effect_step 0x129bd9 0x48 (by decide) 7 (.rip 0xd7fa9) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129be0 [0x48, 0x8D, 0x75, 0xD0] (fun s => s.RIP = 0x129be0) (leaR64Effect 0x129be0 6 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x129be0 6 (.base 5 (.d8 0xd0))).toInstrSpec (lea_r64_effect_step 0x129be0 0x48 (by decide) 6 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x129be4 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x129be4) (movR64R64Effect 0x129be4 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x129be4 2 1).toInstrSpec (mov_r64_r64_effect_step 0x129be4 0x48 0xca (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x129be7 [0xFF, 0x15, 0xF3, 0xA1, 0x0D, 0x00] (GoesTo (CallMemPre 0x129be7 (.rip 0xda1f3)) (callEffect (callMemPtr 0x129be7 (.rip 0xda1f3)) (0x129be7 + BitVec.ofNat 64 (callMemLen (.rip 0xda1f3)))) 0x129770) (callEffect (callMemPtr 0x129be7 (.rip 0xda1f3)) (0x129be7 + BitVec.ofNat 64 (callMemLen (.rip 0xda1f3))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x129be7 (.rip 0xda1f3)).toInstrSpec (call_m64_effect_step 0x129be7 (.rip 0xda1f3) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x129bb6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x129bba) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x129bbe) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x129bc2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x129bc9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x129bcd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x129bd1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x129bd5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x129bd9) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6), (7, 65)]) (p' := 0x129be0) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 67), (7, 65)]) (p' := 0x129be4) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 58), (1, 1), (2, 69), (4, 4), (5, 5), (6, 67), (7, 65)]) (p' := 0x129be7) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 58), (1, 1), (2, 69), (4, 71), (5, 5), (6, 67), (7, 65)]) (p' := 0x129770) f12 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l129bb2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129bb2 :=
  Rest.liftedBlock (rest_l129bb2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129bb2 x hx)

theorem rest_l129bed [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129bed bytes_l129bed) (entryMap (live .l129bed))
      13 0x129bed bytes_l129bed b_l129bed := by
  have f0 : InstrSpec 0x129bed [0x48, 0x89, 0x75, 0xF8] (StorePre 0x129bed 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x129bed + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129bed 6 (.base 5 (.d8 0xf8)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129bed 6 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x129bed 0x48 (by decide) 6 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x129bf1 [0x48, 0x89, 0x55, 0xF0] (StorePre 0x129bf1 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x129bf1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129bf1 2 (.base 5 (.d8 0xf0)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129bf1 2 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x129bf1 0x48 (by decide) 2 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x129bf5 [0x48, 0x8D, 0x45, 0xF8] (fun s => s.RIP = 0x129bf5) (leaR64Effect 0x129bf5 0 (.base 5 (.d8 0xf8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129bf5 0 (.base 5 (.d8 0xf8))).toInstrSpec (lea_r64_effect_step 0x129bf5 0x48 (by decide) 0 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129bf9 [0x48, 0x89, 0x45, 0xD0] (StorePre 0x129bf9 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x129bf9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129bf9 0 (.base 5 (.d8 0xd0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129bf9 0 (.base 5 (.d8 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x129bf9 0x48 (by decide) 0 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x129bfd [0x48, 0x8D, 0x05, 0x2C, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x129bfd) (leaR64Effect 0x129bfd 0 (.rip 0x82c))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129bfd 0 (.rip 0x82c)).toInstrSpec (lea_r64_effect_step 0x129bfd 0x48 (by decide) 0 (.rip 0x82c) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x129c04 [0x48, 0x89, 0x45, 0xD8] (StorePre 0x129c04 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x129c04 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129c04 0 (.base 5 (.d8 0xd8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129c04 0 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x129c04 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x129c08 [0x48, 0x8D, 0x55, 0xF0] (fun s => s.RIP = 0x129c08) (leaR64Effect 0x129c08 2 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x129c08 2 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x129c08 0x48 (by decide) 2 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x129c0c [0x48, 0x89, 0x55, 0xE0] (StorePre 0x129c0c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x129c0c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129c0c 2 (.base 5 (.d8 0xe0)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129c0c 2 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x129c0c 0x48 (by decide) 2 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x129c10 [0x48, 0x89, 0x45, 0xE8] (StorePre 0x129c10 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x129c10 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129c10 0 (.base 5 (.d8 0xe8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129c10 0 (.base 5 (.d8 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x129c10 0x48 (by decide) 0 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x129c14 [0x48, 0x8D, 0x3D, 0x37, 0x7F, 0x0D, 0x00] (fun s => s.RIP = 0x129c14) (leaR64Effect 0x129c14 7 (.rip 0xd7f37))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x129c14 7 (.rip 0xd7f37)).toInstrSpec (lea_r64_effect_step 0x129c14 0x48 (by decide) 7 (.rip 0xd7f37) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129c1b [0x48, 0x8D, 0x75, 0xD0] (fun s => s.RIP = 0x129c1b) (leaR64Effect 0x129c1b 6 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x129c1b 6 (.base 5 (.d8 0xd0))).toInstrSpec (lea_r64_effect_step 0x129c1b 0x48 (by decide) 6 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x129c1f [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x129c1f) (movR64R64Effect 0x129c1f 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x129c1f 2 1).toInstrSpec (mov_r64_r64_effect_step 0x129c1f 0x48 0xca (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x129c22 [0xFF, 0x15, 0xB8, 0xA1, 0x0D, 0x00] (GoesTo (CallMemPre 0x129c22 (.rip 0xda1b8)) (callEffect (callMemPtr 0x129c22 (.rip 0xda1b8)) (0x129c22 + BitVec.ofNat 64 (callMemLen (.rip 0xda1b8)))) 0x129770) (callEffect (callMemPtr 0x129c22 (.rip 0xda1b8)) (0x129c22 + BitVec.ofNat 64 (callMemLen (.rip 0xda1b8))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x129c22 (.rip 0xda1b8)).toInstrSpec (call_m64_effect_step 0x129c22 (.rip 0xda1b8) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6)]) (p' := 0x129bf1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6)]) (p' := 0x129bf5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6)]) (p' := 0x129bf9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6)]) (p' := 0x129bfd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6)]) (p' := 0x129c04) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6)]) (p' := 0x129c08) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6)]) (p' := 0x129c0c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6)]) (p' := 0x129c10) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6)]) (p' := 0x129c14) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6), (7, 65)]) (p' := 0x129c1b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 67), (7, 65)]) (p' := 0x129c1f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 58), (1, 1), (2, 69), (4, 4), (5, 5), (6, 67), (7, 65)]) (p' := 0x129c22) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 58), (1, 1), (2, 69), (4, 71), (5, 5), (6, 67), (7, 65)]) (p' := 0x129770) f12 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l129bed [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129bed :=
  Rest.liftedBlock (rest_l129bed code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129bed x hx)

theorem rest_l129c28 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c28 bytes_l129c28) (entryMap (live .l129c28))
      1 0x129c28 bytes_l129c28 b_l129c28 := by
  have f0 : InstrSpec 0x129c28 [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129c28) (fun _ => nopEffect 0x129c28 8)
      [] [] [.rip] :=
    (nopEffect_footprint 0x129c28 8).toInstrSpec (nop_m_effect_step 0x129c28 [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c30) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l129c28 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c28 :=
  Rest.liftedBlock (rest_l129c28 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c28 x hx)

theorem rest_l129c30 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c30 bytes_l129c30) (entryMap (live .l129c30))
      12 0x129c30 bytes_l129c30 b_l129c30 := by
  have f0 : InstrSpec 0x129c30 [0x55] (PushPre 0x129c30 1) (pushR64Effect 0x129c30 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129c30 1 5).toInstrSpec (push_r64_effect_step 0x129c30 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129c31 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129c31) (movR64R64Effect 0x129c31 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129c31 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129c31 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129c34 [0x41, 0x57] (PushPre 0x129c34 2) (pushR64Effect 0x129c34 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129c34 2 15).toInstrSpec (push_r64_rex_effect_step 0x129c34 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x129c36 [0x41, 0x56] (PushPre 0x129c36 2) (pushR64Effect 0x129c36 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129c36 2 14).toInstrSpec (push_r64_rex_effect_step 0x129c36 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x129c38 [0x41, 0x54] (PushPre 0x129c38 2) (pushR64Effect 0x129c38 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129c38 2 12).toInstrSpec (push_r64_rex_effect_step 0x129c38 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x129c3a [0x53] (PushPre 0x129c3a 1) (pushR64Effect 0x129c3a 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129c3a 1 3).toInstrSpec (push_r64_effect_step 0x129c3a 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x129c3b [0x4C, 0x89, 0xC3] (fun s => s.RIP = 0x129c3b) (movR64R64Effect 0x129c3b 3 8)
      [.gpr 8] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x129c3b 3 8).toInstrSpec (mov_r64_r64_effect_step 0x129c3b 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x129c3e [0x49, 0x89, 0xCE] (fun s => s.RIP = 0x129c3e) (movR64R64Effect 0x129c3e 14 1)
      [.gpr 1] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x129c3e 14 1).toInstrSpec (mov_r64_r64_effect_step 0x129c3e 0x49 0xce (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x129c41 [0x49, 0x89, 0xF4] (fun s => s.RIP = 0x129c41) (movR64R64Effect 0x129c41 12 6)
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x129c41 12 6).toInstrSpec (mov_r64_r64_effect_step 0x129c41 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x129c44 [0x49, 0x89, 0xFF] (fun s => s.RIP = 0x129c44) (movR64R64Effect 0x129c44 15 7)
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x129c44 15 7).toInstrSpec (mov_r64_r64_effect_step 0x129c44 0x49 0xff (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129c47 [0x83, 0xFA, 0xFF] (fun s => s.RIP = 0x129c47) (cmpR32Imm8Effect 0x129c47 3 2 0xff)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x129c47 3 2 0xff).toInstrSpec (cmp_r32_imm8_effect_step 0x129c47 0xfa 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c31) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c34) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c36) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c38) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 60), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c3a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c3b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c3e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 66), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c41) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 68), (13, 13), (14, 66), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c44) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 68), (13, 13), (14, 66), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c47) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 68), (13, 13), (14, 66), (15, 70), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c4a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 74) (jcc_rel8_effect_step 0x129c4a 4 0x12) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129c30 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c30 :=
  Rest.liftedBlock (rest_l129c30 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c30 x hx)

theorem rest_l129c4c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c4c bytes_l129c4c) (entryMap (live .l129c4c))
      2 0x129c4c bytes_l129c4c b_l129c4c := by
  have f0 : InstrSpec 0x129c4c [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x129c4c) (movR64R64Effect 0x129c4c 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x129c4c 7 15).toInstrSpec (mov_r64_r64_effect_step 0x129c4c 0x4c 0xff (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129c4f [0x89, 0xD6] (fun s => s.RIP = 0x129c4f) (movR32R32Effect 0x129c4f 2 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x129c4f 2 6 2).toInstrSpec (mov_r32_r32_effect_step 0x129c4f 0xd6 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (15, 15)]) (p' := 0x129c4f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (15, 15)]) (p' := 0x129c51) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l129c4c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c4c :=
  Rest.liftedBlock (rest_l129c4c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c4c x hx)

theorem rest_l129c56 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c56 bytes_l129c56) (entryMap (live .l129c56))
      4 0x129c56 bytes_l129c56 b_l129c56 := by
  have f0 : InstrSpec 0x129c56 [0x89, 0xC1] (fun s => s.RIP = 0x129c56) (movR32R32Effect 0x129c56 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x129c56 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x129c56 0xc1 (by decide)) pre_rip
  have f1 : InstrSpec 0x129c58 [0xB0, 0x01] (fun s => s.RIP = 0x129c58) (movR8Imm8Effect 0x129c58 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x129c58 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x129c58 0xb0 (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x129c5a [0x84, 0xC9] (fun s => s.RIP = 0x129c5a) (testR8R8Effect 0x129c5a 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x129c5a 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x129c5a 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c58) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c5a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c5c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x129c5c 5 0x1f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129c56 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c56 :=
  Rest.liftedBlock (rest_l129c56 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c56 x hx)

theorem rest_l129c5e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c5e bytes_l129c5e) (entryMap (live .l129c5e))
      2 0x129c5e bytes_l129c5e b_l129c5e := by
  have f0 : InstrSpec 0x129c5e [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x129c5e) (testR64R64Effect 0x129c5e 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x129c5e 14 14).toInstrSpec (test_r64_r64_effect_step 0x129c5e 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c61) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x129c61 4 0x18) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129c5e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c5e :=
  Rest.liftedBlock (rest_l129c5e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c5e x hx)

theorem rest_l129c63 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c63 bytes_l129c63) (entryMap (live .l129c63))
      9 0x129c63 bytes_l129c63 b_l129c63 := by
  have f0 : InstrSpec 0x129c63 [0x49, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x129c63 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x129c63 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x129c63 0 (.sib 12 none 0 (.d8 0x18)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x129c63 0 (.sib 12 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x129c63 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x129c68 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x129c68) (movR64R64Effect 0x129c68 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x129c68 7 15).toInstrSpec (mov_r64_r64_effect_step 0x129c68 0x4c 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129c6b [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x129c6b) (movR64R64Effect 0x129c6b 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x129c6b 6 14).toInstrSpec (mov_r64_r64_effect_step 0x129c6b 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129c6e [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x129c6e) (movR64R64Effect 0x129c6e 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x129c6e 2 3).toInstrSpec (mov_r64_r64_effect_step 0x129c6e 0x48 0xda (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129c71 [0x5B] (PopPre 0x129c71) (popR64Effect 0x129c71 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c71 1 3).toInstrSpec (pop_r64_effect_step 0x129c71 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x129c72 [0x41, 0x5C] (PopPre 0x129c72) (popR64Effect 0x129c72 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c72 2 12).toInstrSpec (pop_r64_rex_effect_step 0x129c72 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x129c74 [0x41, 0x5E] (PopPre 0x129c74) (popR64Effect 0x129c74 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c74 2 14).toInstrSpec (pop_r64_rex_effect_step 0x129c74 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x129c76 [0x41, 0x5F] (PopPre 0x129c76) (popR64Effect 0x129c76 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c76 2 15).toInstrSpec (pop_r64_rex_effect_step 0x129c76 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x129c78 [0x5D] (PopPre 0x129c78) (popR64Effect 0x129c78 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c78 1 5).toInstrSpec (pop_r64_effect_step 0x129c78 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (12, 12), (14, 14), (15, 15)]) (p' := 0x129c68) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (12, 12), (14, 14), (15, 15)]) (p' := 0x129c6b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (12, 12), (14, 14), (15, 15)]) (p' := 0x129c6e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (12, 12), (14, 14), (15, 15)]) (p' := 0x129c71) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(4, 57), (12, 12), (14, 14), (15, 15)]) (p' := 0x129c72) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(4, 59), (14, 14), (15, 15)]) (p' := 0x129c74) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(4, 61), (15, 15)]) (p' := 0x129c76) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(4, 63)]) (p' := 0x129c78) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := []) (p' := 0x129c79) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l129c63 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c63 :=
  Rest.liftedBlock (rest_l129c63 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c63 x hx)

theorem rest_l129c7b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c7b bytes_l129c7b) (entryMap (live .l129c7b))
      1 0x129c7b bytes_l129c7b b_l129c7b := by
  have f0 : InstrSpec 0x129c7b [0x31, 0xC0] (fun s => s.RIP = 0x129c7b) (xorR32R32Effect 0x129c7b 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129c7b 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x129c7b 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c7d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l129c7b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c7b :=
  Rest.liftedBlock (rest_l129c7b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c7b x hx)

theorem rest_l129c7d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c7d bytes_l129c7d) (entryMap (live .l129c7d))
      6 0x129c7d bytes_l129c7d b_l129c7d := by
  have f0 : InstrSpec 0x129c7d [0x5B] (PopPre 0x129c7d) (popR64Effect 0x129c7d 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c7d 1 3).toInstrSpec (pop_r64_effect_step 0x129c7d 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129c7e [0x41, 0x5C] (PopPre 0x129c7e) (popR64Effect 0x129c7e 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c7e 2 12).toInstrSpec (pop_r64_rex_effect_step 0x129c7e 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x129c80 [0x41, 0x5E] (PopPre 0x129c80) (popR64Effect 0x129c80 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c80 2 14).toInstrSpec (pop_r64_rex_effect_step 0x129c80 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x129c82 [0x41, 0x5F] (PopPre 0x129c82) (popR64Effect 0x129c82 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c82 2 15).toInstrSpec (pop_r64_rex_effect_step 0x129c82 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x129c84 [0x5D] (PopPre 0x129c84) (popR64Effect 0x129c84 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c84 1 5).toInstrSpec (pop_r64_effect_step 0x129c84 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x129c85 [0xC3] (RetPre 0x129c85) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x129c85).toInstrSpec (ret_effect_step 0x129c85) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 54), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c7e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 57) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c80) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 60), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 13), (14, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c82) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 13), (14, 59), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c84) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 66), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 13), (14, 59), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c85) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 69), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 13), (14, 59), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l129c7d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c7d :=
  Rest.liftedBlock (rest_l129c7d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c7d x hx)

theorem rest_l129c90 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c90 bytes_l129c90) (entryMap (live .l129c90))
      15 0x129c90 bytes_l129c90 b_l129c90 := by
  have f0 : InstrSpec 0x129c90 [0x55] (PushPre 0x129c90 1) (pushR64Effect 0x129c90 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129c90 1 5).toInstrSpec (push_r64_effect_step 0x129c90 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129c91 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129c91) (movR64R64Effect 0x129c91 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129c91 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129c91 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129c94 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x129c94) (subR64Imm8Effect 0x129c94 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x129c94 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x129c94 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129c98 [0x48, 0x89, 0x75, 0xF8] (StorePre 0x129c98 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x129c98 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129c98 6 (.base 5 (.d8 0xf8)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129c98 6 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x129c98 0x48 (by decide) 6 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x129c9c [0x48, 0x89, 0x7D, 0xF0] (StorePre 0x129c9c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x129c9c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129c9c 7 (.base 5 (.d8 0xf0)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129c9c 7 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x129c9c 0x48 (by decide) 7 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x129ca0 [0x48, 0x8D, 0x45, 0xF8] (fun s => s.RIP = 0x129ca0) (leaR64Effect 0x129ca0 0 (.base 5 (.d8 0xf8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129ca0 0 (.base 5 (.d8 0xf8))).toInstrSpec (lea_r64_effect_step 0x129ca0 0x48 (by decide) 0 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129ca4 [0x48, 0x89, 0x45, 0xD0] (StorePre 0x129ca4 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x129ca4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129ca4 0 (.base 5 (.d8 0xd0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129ca4 0 (.base 5 (.d8 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x129ca4 0x48 (by decide) 0 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x129ca8 [0x48, 0x8D, 0x05, 0x81, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x129ca8) (leaR64Effect 0x129ca8 0 (.rip 0x781))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129ca8 0 (.rip 0x781)).toInstrSpec (lea_r64_effect_step 0x129ca8 0x48 (by decide) 0 (.rip 0x781) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x129caf [0x48, 0x89, 0x45, 0xD8] (StorePre 0x129caf 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x129caf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129caf 0 (.base 5 (.d8 0xd8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129caf 0 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x129caf 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x129cb3 [0x48, 0x8D, 0x4D, 0xF0] (fun s => s.RIP = 0x129cb3) (leaR64Effect 0x129cb3 1 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x129cb3 1 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x129cb3 0x48 (by decide) 1 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129cb7 [0x48, 0x89, 0x4D, 0xE0] (StorePre 0x129cb7 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x129cb7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129cb7 1 (.base 5 (.d8 0xe0)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129cb7 1 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x129cb7 0x48 (by decide) 1 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x129cbb [0x48, 0x89, 0x45, 0xE8] (StorePre 0x129cbb 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x129cbb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129cbb 0 (.base 5 (.d8 0xe8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129cbb 0 (.base 5 (.d8 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x129cbb 0x48 (by decide) 0 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x129cbf [0x48, 0x8D, 0x3D, 0x9C, 0x80, 0x0D, 0x00] (fun s => s.RIP = 0x129cbf) (leaR64Effect 0x129cbf 7 (.rip 0xd809c))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x129cbf 7 (.rip 0xd809c)).toInstrSpec (lea_r64_effect_step 0x129cbf 0x48 (by decide) 7 (.rip 0xd809c) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x129cc6 [0x48, 0x8D, 0x75, 0xD0] (fun s => s.RIP = 0x129cc6) (leaR64Effect 0x129cc6 6 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x129cc6 6 (.base 5 (.d8 0xd0))).toInstrSpec (lea_r64_effect_step 0x129cc6 0x48 (by decide) 6 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x129cca [0xFF, 0x15, 0x10, 0xA1, 0x0D, 0x00] (GoesTo (CallMemPre 0x129cca (.rip 0xda110)) (callEffect (callMemPtr 0x129cca (.rip 0xda110)) (0x129cca + BitVec.ofNat 64 (callMemLen (.rip 0xda110)))) 0x129770) (callEffect (callMemPtr 0x129cca (.rip 0xda110)) (0x129cca + BitVec.ofNat 64 (callMemLen (.rip 0xda110))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x129cca (.rip 0xda110)).toInstrSpec (call_m64_effect_step 0x129cca (.rip 0xda110) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 53), (5, 5), (6, 6), (7, 7)]) (p' := 0x129c91) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 53), (5, 55), (6, 6), (7, 7)]) (p' := 0x129c94) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129c98) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129c9c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129ca0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129ca4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129ca8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129caf) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129cb3) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129cb7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129cbb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129cbf) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 57), (5, 55), (6, 6), (7, 71)]) (p' := 0x129cc6) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 57), (5, 55), (6, 73), (7, 71)]) (p' := 0x129cca) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 75), (5, 55), (6, 73), (7, 71)]) (p' := 0x129770) f14 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l129c90 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c90 :=
  Rest.liftedBlock (rest_l129c90 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c90 x hx)

theorem rest_l129cd0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129cd0 bytes_l129cd0) (entryMap (live .l129cd0))
      8 0x129cd0 bytes_l129cd0 b_l129cd0 := by
  have f0 : InstrSpec 0x129cd0 [0x55] (PushPre 0x129cd0 1) (pushR64Effect 0x129cd0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129cd0 1 5).toInstrSpec (push_r64_effect_step 0x129cd0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129cd1 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129cd1) (movR64R64Effect 0x129cd1 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129cd1 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129cd1 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129cd4 [0x48, 0x83, 0xEC, 0x10] (fun s => s.RIP = 0x129cd4) (subR64Imm8Effect 0x129cd4 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x129cd4 4 0x10).toInstrSpec (sub_r64_imm8_effect_step 0x129cd4 0x48 0xec 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129cd8 [0x0F, 0xB6, 0x0F] (LoadPre 0x129cd8 (fun s => AddrMode.addr (.base 7 .none) s (0x129cd8 + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x129cd8 3 1 (.base 7 .none))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x129cd8 3 1 (.base 7 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x129cd8 1 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x129cdb [0xB8, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129cdb) (movR32Imm32Effect 0x129cdb 5 0 0x3)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x129cdb 5 0 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x129cdb 0xb8 (by decide) 0x3) pre_rip
  have f5 : InstrSpec 0x129ce0 [0x89, 0xCA] (fun s => s.RIP = 0x129ce0) (movR32R32Effect 0x129ce0 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x129ce0 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x129ce0 0xca (by decide)) pre_rip
  have f6 : InstrSpec 0x129ce2 [0x80, 0xF9, 0x0A] (fun s => s.RIP = 0x129ce2) (cmpR8Imm8Effect 0x129ce2 3 1 0xa)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x129ce2 3 1 0xa).toInstrSpec (cmp_r8_imm8_effect_step 0x129ce2 0xf9 0xa (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cd1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 53), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cd4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cd8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 59), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cdb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 59), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ce0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 59), (2, 63), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ce2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 59), (2, 63), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ce5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 67) (jcc_rel8_effect_step 0x129ce5 2 0x2c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129cd0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129cd0 :=
  Rest.liftedBlock (rest_l129cd0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129cd0 x hx)

theorem rest_l129ce7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129ce7 bytes_l129ce7) (entryMap (live .l129ce7))
      12 0x129ce7 bytes_l129ce7 b_l129ce7 := by
  have f0 : InstrSpec 0x129ce7 [0x0F, 0xB6, 0xC1] (fun s => s.RIP = 0x129ce7) (movzxR32R8Effect 0x129ce7 3 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x129ce7 3 0 1).toInstrSpec (movzx_r32_r8_effect_step 0x129ce7 0xc1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129cea [0x8D, 0x14, 0x80] (fun s => s.RIP = 0x129cea) (leaR32Effect 0x129cea 3 2 (.sib 0 (some 0) 2 .none))
      [.gpr 0, .gpr 0] [] [.reg 2, .rip] :=
    (leaR32Effect_footprint 0x129cea 3 2 (.sib 0 (some 0) 2 .none)).toInstrSpec (lea_r32_effect_step 0x129cea 2 (.sib 0 (some 0) 2 .none) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129ced [0x8D, 0x14, 0xD0] (fun s => s.RIP = 0x129ced) (leaR32Effect 0x129ced 3 2 (.sib 0 (some 2) 3 .none))
      [.gpr 0, .gpr 2] [] [.reg 2, .rip] :=
    (leaR32Effect_footprint 0x129ced 3 2 (.sib 0 (some 2) 3 .none)).toInstrSpec (lea_r32_effect_step 0x129ced 2 (.sib 0 (some 2) 3 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129cf0 [0xC1, 0xEA, 0x0C] (fun s => s.RIP = 0x129cf0) (shrR32Effect 0x129cf0 3 2 12)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x129cf0 3 2 12).toInstrSpec (shr_r32_imm8_effect_step 0x129cf0 0xea 0xc (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129cf3 [0x6B, 0xC2, 0x64] (fun s => s.RIP = 0x129cf3) (imulR32R32Imm8Effect 0x129cf3 3 0 2 0x64)
      [.gpr 2] [] [.reg 0, .flags, .rip] :=
    (imulR32R32Imm8Effect_footprint 0x129cf3 3 0 2 0x64).toInstrSpec (imul_r32_r32_imm8_effect_step 0x129cf3 0xc2 (by decide) 0x64) pre_rip
  have f5 : InstrSpec 0x129cf6 [0x89, 0xCF] (fun s => s.RIP = 0x129cf6) (movR32R32Effect 0x129cf6 2 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x129cf6 2 7 1).toInstrSpec (mov_r32_r32_effect_step 0x129cf6 0xcf (by decide)) pre_rip
  have f6 : InstrSpec 0x129cf8 [0x40, 0x28, 0xC7] (fun s => s.RIP = 0x129cf8) (subR8R8Effect 0x129cf8 3 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (subR8R8Effect_footprint 0x129cf8 3 7 0).toInstrSpec (sub_r8_r8_rex_effect_step 0x129cf8 0x40 0xc7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x129cfb [0x40, 0x0F, 0xB6, 0xC7] (fun s => s.RIP = 0x129cfb) (movzxR32R8Effect 0x129cfb 4 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x129cfb 4 0 7).toInstrSpec (movzx_r32_r8_rex_effect_step 0x129cfb 0x40 (by decide) 0xc7 (by decide)) pre_rip
  have f8 : InstrSpec 0x129cff [0x48, 0x8D, 0x3D, 0x3D, 0x9F, 0x0D, 0x00] (fun s => s.RIP = 0x129cff) (leaR64Effect 0x129cff 7 (.rip 0xd9f3d))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x129cff 7 (.rip 0xd9f3d)).toInstrSpec (lea_r64_effect_step 0x129cff 0x48 (by decide) 7 (.rip 0xd9f3d) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x129d06 [0x0F, 0xB7, 0x04, 0x47] (LoadPre 0x129d06 (fun s => AddrMode.addr (.sib 7 (some 0) 1 .none) s (0x129d06 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x129d06 4 0 (.sib 7 (some 0) 1 .none))
      [.gpr 7, .gpr 0] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x129d06 4 0 (.sib 7 (some 0) 1 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x129d06 0 (.sib 7 (some 0) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x129d0a [0x66, 0x89, 0x45, 0xFE] (StorePre 0x129d0a 4 (fun s => AddrMode.addr (.base 5 (.d8 0xfe)) s (0x129d0a + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x129d0a 4 0 (.base 5 (.d8 0xfe)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM16R16Effect_footprint 0x129d0a 4 0 (.base 5 (.d8 0xfe))).toInstrSpec (mov_m16_r16_effect_step 0x129d0a 0 (.base 5 (.d8 0xfe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x129d0e [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129d0e) (movR32Imm32Effect 0x129d0e 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x129d0e 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x129d0e 0xb8 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cea) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ced) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cf0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cf3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cf6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cf8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cfb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cff) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 69), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d06) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 69), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d0a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 69), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d0e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 69), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d13) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 76) (by decide) rfl

theorem block_l129ce7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129ce7 :=
  Rest.liftedBlock (rest_l129ce7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129ce7 x hx)

theorem rest_l129d13 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129d13 bytes_l129d13) (entryMap (live .l129d13))
      6 0x129d13 bytes_l129d13 b_l129d13 := by
  have f0 : InstrSpec 0x129d13 [0x84, 0xD2] (fun s => s.RIP = 0x129d13) (testR8R8Effect 0x129d13 2 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x129d13 2 2 2).toInstrSpec (test_r8_r8_effect_step 0x129d13 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129d15 [0x40, 0x0F, 0x94, 0xC7] (fun s => s.RIP = 0x129d15) (atFlags (condHolds 4) (setccR8Effect 0x129d15 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x129d15 4 7 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x129d15 4 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f2 : InstrSpec 0x129d19 [0x84, 0xC9] (fun s => s.RIP = 0x129d19) (testR8R8Effect 0x129d19 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x129d19 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x129d19 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129d1b [0x0F, 0x95, 0xC1] (fun s => s.RIP = 0x129d1b) (atFlags (condHolds 5) (setccR8Effect 0x129d1b 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x129d1b 3 1 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x129d1b 5 0xc1 (by decide) (by decide) c)) pre_rip
  have f4 : InstrSpec 0x129d1e [0x40, 0x84, 0xF9] (fun s => s.RIP = 0x129d1e) (testR8R8Effect 0x129d1e 3 1 7)
      [.gpr 1, .gpr 7] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x129d1e 3 1 7).toInstrSpec (test_r8_r8_rex_effect_step 0x129d1e 0x40 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d15) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d19) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d1b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d1e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d21) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x129d21 5 0x16) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129d13 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129d13 :=
  Rest.liftedBlock (rest_l129d13 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129d13 x hx)

theorem rest_l129d23 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129d23 bytes_l129d23) (entryMap (live .l129d23))
      5 0x129d23 bytes_l129d23 b_l129d23 := by
  have f0 : InstrSpec 0x129d23 [0x0F, 0xB6, 0xCA] (fun s => s.RIP = 0x129d23) (movzxR32R8Effect 0x129d23 3 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x129d23 3 1 2).toInstrSpec (movzx_r32_r8_effect_step 0x129d23 0xca (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129d26 [0x48, 0x8D, 0x15, 0x16, 0x9F, 0x0D, 0x00] (fun s => s.RIP = 0x129d26) (leaR64Effect 0x129d26 2 (.rip 0xd9f16))
      [] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x129d26 2 (.rip 0xd9f16)).toInstrSpec (lea_r64_effect_step 0x129d26 0x48 (by decide) 2 (.rip 0xd9f16) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129d2d [0x0F, 0xB6, 0x4C, 0x4A, 0x01] (LoadPre 0x129d2d (fun s => AddrMode.addr (.sib 2 (some 1) 1 (.d8 0x1)) s (0x129d2d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x129d2d 5 1 (.sib 2 (some 1) 1 (.d8 0x1)))
      [.gpr 2, .gpr 1] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x129d2d 5 1 (.sib 2 (some 1) 1 (.d8 0x1))).toInstrSpec (movzx_r32_m8_effect_step 0x129d2d 1 (.sib 2 (some 1) 1 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x129d32 [0x88, 0x4C, 0x05, 0xFC] (StorePre 0x129d32 4 (fun s => AddrMode.addr (.sib 5 (some 0) 0 (.d8 0xfc)) s (0x129d32 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x129d32 4 1 (.sib 5 (some 0) 0 (.d8 0xfc)))
      [.gpr 1, .gpr 5, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x129d32 4 1 (.sib 5 (some 0) 0 (.d8 0xfc))).toInstrSpec (mov_m8_r8_effect_step 0x129d32 1 (by decide) (.sib 5 (some 0) 0 (.d8 0xfc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x129d36 [0x48, 0xFF, 0xC8] (fun s => s.RIP = 0x129d36) (decR64Effect 0x129d36 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (decR64Effect_footprint 0x129d36 0).toInstrSpec (dec_r64_effect_step 0x129d36 0x48 0xc8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d26) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d2d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d32) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d36) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d39) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 62) (by decide) rfl

theorem block_l129d23 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129d23 :=
  Rest.liftedBlock (rest_l129d23 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129d23 x hx)

theorem rest_l129d39 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129d39 bytes_l129d39) (entryMap (live .l129d39))
      9 0x129d39 bytes_l129d39 b_l129d39 := by
  have f0 : InstrSpec 0x129d39 [0x41, 0xB9, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129d39) (movR32Imm32Effect 0x129d39 6 9 0x3)
      [] [] [.reg 9, .rip] :=
    (movR32Imm32Effect_footprint 0x129d39 6 9 0x3).toInstrSpec (mov_r32_imm32_rex_effect_step 0x129d39 0x41 0xb9 (by decide) (by decide) 0x3) pre_rip
  have f1 : InstrSpec 0x129d3f [0x49, 0x29, 0xC1] (fun s => s.RIP = 0x129d3f) (subR64R64Effect 0x129d3f 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x129d3f 9 0).toInstrSpec (sub_r64_r64_effect_step 0x129d3f 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129d42 [0x4C, 0x8D, 0x04, 0x28] (fun s => s.RIP = 0x129d42) (leaR64Effect 0x129d42 8 (.sib 0 (some 5) 0 .none))
      [.gpr 0, .gpr 5] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x129d42 8 (.sib 0 (some 5) 0 .none)).toInstrSpec (lea_r64_effect_step 0x129d42 0x4c (by decide) 0 (.sib 0 (some 5) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129d46 [0x49, 0x83, 0xC0, 0xFD] (fun s => s.RIP = 0x129d46) (addR64Imm8Effect 0x129d46 8 0xfd)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x129d46 8 0xfd).toInstrSpec (add_r64_imm8_effect_step 0x129d46 0x49 0xc0 0xfd (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129d4a [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129d4a) (movR32Imm32Effect 0x129d4a 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x129d4a 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x129d4a 0xba (by decide) 0x1) pre_rip
  have f5 : InstrSpec 0x129d4f [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x129d4f) (movR64R64Effect 0x129d4f 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x129d4f 7 6).toInstrSpec (mov_r64_r64_effect_step 0x129d4f 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129d52 [0xBE, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129d52) (movR32Imm32Effect 0x129d52 5 6 0x1)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x129d52 5 6 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x129d52 0xbe (by decide) 0x1) pre_rip
  have f7 : InstrSpec 0x129d57 [0x31, 0xC9] (fun s => s.RIP = 0x129d57) (xorR32R32Effect 0x129d57 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129d57 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x129d57 0xc9 (by decide)) pre_rip
  have f8 : InstrSpec 0x129d59 [0xFF, 0x15, 0x89, 0xA0, 0x0D, 0x00] (GoesTo (CallMemPre 0x129d59 (.rip 0xda089)) (callEffect (callMemPtr 0x129d59 (.rip 0xda089)) (0x129d59 + BitVec.ofNat 64 (callMemLen (.rip 0xda089)))) 0x128b20) (callEffect (callMemPtr 0x129d59 (.rip 0xda089)) (0x129d59 + BitVec.ofNat 64 (callMemLen (.rip 0xda089))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x129d59 (.rip 0xda089)).toInstrSpec (call_m64_effect_step 0x129d59 (.rip 0xda089) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x128b20
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d3f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d42) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 57), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d46) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d4a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d4f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d52) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d57) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 61), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d59) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 67), (2, 61), (3, 3), (4, 69), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b20) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l129d39 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129d39 :=
  Rest.liftedBlock (rest_l129d39 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129d39 x hx)

theorem rest_l129d5f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129d5f bytes_l129d5f) (entryMap (live .l129d5f))
      3 0x129d5f bytes_l129d5f b_l129d5f := by
  have f0 : InstrSpec 0x129d5f [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x129d5f) (addR64Imm8Effect 0x129d5f 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x129d5f 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x129d5f 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129d63 [0x5D] (PopPre 0x129d63) (popR64Effect 0x129d63 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129d63 1 5).toInstrSpec (pop_r64_effect_step 0x129d63 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x129d64 [0xC3] (RetPre 0x129d64) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x129d64).toInstrSpec (ret_effect_step 0x129d64) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d63) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d64) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f2 (by decide) rfl rfl rfl (by decide)

theorem block_l129d5f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129d5f :=
  Rest.liftedBlock (rest_l129d5f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129d5f x hx)

theorem rest_l12a050 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a050 bytes_l12a050) (entryMap (live .l12a050))
      4 0x12a050 bytes_l12a050 b_l12a050 := by
  have f0 : InstrSpec 0x12a050 [0x48, 0x8B, 0x07] (LoadPre 0x12a050 (fun s => AddrMode.addr (.base 7 .none) s (0x12a050 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a050 0 (.base 7 .none))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12a050 0 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a050 0x48 (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12a053 [0x48, 0x8B, 0x4F, 0x08] (LoadPre 0x12a053 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x12a053 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a053 1 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12a053 1 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12a053 0x48 (by decide) 1 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12a057 [0x48, 0x8B, 0x49, 0x18] (LoadPre 0x12a057 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x12a057 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a057 1 (.base 1 (.d8 0x18)))
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12a057 1 (.base 1 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x12a057 0x48 (by decide) 1 (.base 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12a05b [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x12a05b) (movR64R64Effect 0x12a05b 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12a05b 7 0).toInstrSpec (mov_r64_r64_effect_step 0x12a05b 0x48 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (7, 7)]) (p' := 0x12a053) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (7, 7)]) (p' := 0x12a057) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (7, 7)]) (p' := 0x12a05b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53)]) (p' := 0x12a05e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l12a050 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a050 :=
  Rest.liftedBlock (rest_l12a050 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a050 x hx)

theorem rest_l12a070 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a070 bytes_l12a070) (entryMap (live .l12a070))
      5 0x12a070 bytes_l12a070 b_l12a070 := by
  have f0 : InstrSpec 0x12a070 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x12a070) (movR64R64Effect 0x12a070 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12a070 0 6).toInstrSpec (mov_r64_r64_effect_step 0x12a070 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a073 [0x48, 0x8B, 0x37] (LoadPre 0x12a073 (fun s => AddrMode.addr (.base 7 .none) s (0x12a073 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a073 6 (.base 7 .none))
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12a073 6 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a073 0x48 (by decide) 6 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12a076 [0x48, 0x8B, 0x57, 0x08] (LoadPre 0x12a076 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x12a076 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a076 2 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12a076 2 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12a076 0x48 (by decide) 2 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12a07a [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x12a07a) (movR64R64Effect 0x12a07a 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12a07a 7 0).toInstrSpec (mov_r64_r64_effect_step 0x12a07a 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a07d [0xFF, 0x25, 0x85, 0x9D, 0x0D, 0x00] (GoesTo (JmpMemPre 0x12a07d 6 (.rip 0xd9d85)) (jmpM64Effect 0x12a07d 6 (.rip 0xd9d85)) 0x129100) (jmpM64Effect 0x12a07d 6 (.rip 0xd9d85))
      [] [] [.rip] :=
    ((jmpM64Effect_footprint 0x12a07d 6 (.rip 0xd9d85)).toInstrSpec (jmp_m64_effect_step 0x12a07d (.rip 0xd9d85) (by decide) (by decide) (by decide)) (JmpMemPre.of_addr rfl)).goesTo 0x129100
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a073) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a076) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a07a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a07d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129100) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 62) (by decide) rfl

theorem block_l12a070 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a070 :=
  Rest.liftedBlock (rest_l12a070 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a070 x hx)

theorem rest_l12a100 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a100 bytes_l12a100) (entryMap (live .l12a100))
      6 0x12a100 bytes_l12a100 b_l12a100 := by
  have f0 : InstrSpec 0x12a100 [0x48, 0x8B, 0x06] (LoadPre 0x12a100 (fun s => AddrMode.addr (.base 6 .none) s (0x12a100 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a100 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12a100 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a100 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12a103 [0x48, 0x8B, 0x76, 0x08] (LoadPre 0x12a103 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x12a103 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a103 6 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12a103 6 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12a103 0x48 (by decide) 6 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12a107 [0x48, 0x8B, 0x17] (LoadPre 0x12a107 (fun s => AddrMode.addr (.base 7 .none) s (0x12a107 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a107 2 (.base 7 .none))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12a107 2 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a107 0x48 (by decide) 2 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12a10a [0x48, 0x8B, 0x4F, 0x08] (LoadPre 0x12a10a (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x12a10a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a10a 1 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12a10a 1 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12a10a 0x48 (by decide) 1 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x12a10e [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x12a10e) (movR64R64Effect 0x12a10e 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12a10e 7 0).toInstrSpec (mov_r64_r64_effect_step 0x12a10e 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12a111 [0xFF, 0x25, 0x11, 0x9D, 0x0D, 0x00] (GoesTo (JmpMemPre 0x12a111 6 (.rip 0xd9d11)) (jmpM64Effect 0x12a111 6 (.rip 0xd9d11)) 0x1293a0) (jmpM64Effect 0x12a111 6 (.rip 0xd9d11))
      [] [] [.rip] :=
    ((jmpM64Effect_footprint 0x12a111 6 (.rip 0xd9d11)).toInstrSpec (jmp_m64_effect_step 0x12a111 (.rip 0xd9d11) (by decide) (by decide) (by decide)) (JmpMemPre.of_addr rfl)).goesTo 0x1293a0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a103) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a107) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a10a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a10e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a111) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293a0) f5 (fun _ h => h.2) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 64) (by decide) rfl

theorem block_l12a100 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a100 :=
  Rest.liftedBlock (rest_l12a100 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a100 x hx)

theorem rest_l12a430 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a430 bytes_l12a430) (entryMap (live .l12a430))
      10 0x12a430 bytes_l12a430 b_l12a430 := by
  have f0 : InstrSpec 0x12a430 [0x55] (PushPre 0x12a430 1) (pushR64Effect 0x12a430 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12a430 1 5).toInstrSpec (push_r64_effect_step 0x12a430 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x12a431 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x12a431) (movR64R64Effect 0x12a431 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x12a431 5 4).toInstrSpec (mov_r64_r64_effect_step 0x12a431 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a434 [0x53] (PushPre 0x12a434 1) (pushR64Effect 0x12a434 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12a434 1 3).toInstrSpec (push_r64_effect_step 0x12a434 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x12a435 [0x48, 0x83, 0xEC, 0x18] (fun s => s.RIP = 0x12a435) (subR64Imm8Effect 0x12a435 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x12a435 4 0x18).toInstrSpec (sub_r64_imm8_effect_step 0x12a435 0x48 0xec 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a439 [0x4C, 0x8B, 0x07] (LoadPre 0x12a439 (fun s => AddrMode.addr (.base 7 .none) s (0x12a439 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a439 8 (.base 7 .none))
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x12a439 8 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a439 0x4c (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x12a43c [0xB8, 0x14, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a43c) (movR32Imm32Effect 0x12a43c 5 0 0x14)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x12a43c 5 0 0x14).toInstrSpec (mov_r32_imm32_effect_step 0x12a43c 0xb8 (by decide) 0x14) pre_rip
  have f6 : InstrSpec 0x12a441 [0x48, 0x8D, 0x3D, 0xFB, 0x97, 0x0D, 0x00] (fun s => s.RIP = 0x12a441) (leaR64Effect 0x12a441 7 (.rip 0xd97fb))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x12a441 7 (.rip 0xd97fb)).toInstrSpec (lea_r64_effect_step 0x12a441 0x48 (by decide) 7 (.rip 0xd97fb) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12a448 [0x4C, 0x89, 0xC2] (fun s => s.RIP = 0x12a448) (movR64R64Effect 0x12a448 2 8)
      [.gpr 8] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12a448 2 8).toInstrSpec (mov_r64_r64_effect_step 0x12a448 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12a44b [0x49, 0x81, 0xF8, 0xE8, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x12a44b) (cmpR64Imm32Effect 0x12a44b 8 0x3e8)
      [.gpr 8] [] [.flags, .rip] :=
    (cmpR64Imm32Effect_footprint 0x12a44b 8 0x3e8).toInstrSpec (cmp_r64_imm32_effect_step 0x12a44b 0x49 0xf8 0x3e8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a431) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 53), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a434) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a435) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a439) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (8, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a43c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 1), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (8, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a441) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 63), (1, 1), (3, 3), (4, 59), (5, 55), (6, 6), (7, 65), (8, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a448) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 63), (1, 1), (2, 67), (3, 3), (4, 59), (5, 55), (6, 6), (7, 65), (8, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a44b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 63), (1, 1), (2, 67), (3, 3), (4, 59), (5, 55), (6, 6), (7, 65), (8, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a452) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 71) (jcc_rel8_effect_step 0x12a452 2 0x6d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a430 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a430 :=
  Rest.liftedBlock (rest_l12a430 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a430 x hx)

theorem rest_l12a454 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a454 bytes_l12a454) (entryMap (live .l12a454))
      3 0x12a454 bytes_l12a454 b_l12a454 := by
  have f0 : InstrSpec 0x12a454 [0x49, 0xB9, 0x4B, 0x59, 0x86, 0x38, 0xD6, 0xC5, 0x6D, 0x34] (fun s => s.RIP = 0x12a454) (movR64Imm64Effect 0x12a454 9 0x346dc5d63886594b)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x12a454 9 0x346dc5d63886594b).toInstrSpec (mov_r64_imm64_effect_step 0x12a454 0x49 0xb9 (by decide) (by decide) 0x346dc5d63886594b) pre_rip
  have f1 : InstrSpec 0x12a45e [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x12a45e) (movR64R64Effect 0x12a45e 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a45e 1 8).toInstrSpec (mov_r64_r64_effect_step 0x12a45e 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a461 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a461) (fun _ => nopEffect 0x12a461 15)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12a461 15).toInstrSpec (nop_m_effect_step 0x12a461 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a45e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a461) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a470) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l12a454 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a454 :=
  Rest.liftedBlock (rest_l12a454 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a454 x hx)

theorem rest_l12a470 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a470 bytes_l12a470) (entryMap (live .l12a470))
      20 0x12a470 bytes_l12a470 b_l12a470 := by
  have f0 : InstrSpec 0x12a470 [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x12a470) (movR64R64Effect 0x12a470 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x12a470 10 0).toInstrSpec (mov_r64_r64_effect_step 0x12a470 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a473 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x12a473) (movR64R64Effect 0x12a473 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12a473 0 1).toInstrSpec (mov_r64_r64_effect_step 0x12a473 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a476 [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x12a476) (mulR64Effect 0x12a476 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x12a476 9).toInstrSpec (mul_r64_effect_step 0x12a476 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12a479 [0x48, 0xC1, 0xEA, 0x0B] (fun s => s.RIP = 0x12a479) (shrR64Effect 0x12a479 4 2 11)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x12a479 4 2 11).toInstrSpec (shr_r64_imm8_effect_step 0x12a479 0x48 0xea 0xb (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a47d [0x69, 0xC2, 0x10, 0x27, 0x00, 0x00] (fun s => s.RIP = 0x12a47d) (imulR32R32Imm32Effect 0x12a47d 6 0 2 0x2710)
      [.gpr 2] [] [.reg 0, .flags, .rip] :=
    (imulR32R32Imm32Effect_footprint 0x12a47d 6 0 2 0x2710).toInstrSpec (imul_r32_r32_imm32_effect_step 0x12a47d 0xc2 (by decide) 0x2710) pre_rip
  have f5 : InstrSpec 0x12a483 [0x41, 0x89, 0xCB] (fun s => s.RIP = 0x12a483) (movR32R32Effect 0x12a483 3 11 1)
      [.gpr 1] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x12a483 3 11 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x12a483 0x41 0xcb (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12a486 [0x41, 0x29, 0xC3] (fun s => s.RIP = 0x12a486) (subR32R32Effect 0x12a486 3 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (subR32R32Effect_footprint 0x12a486 3 11 0).toInstrSpec (sub_r32_r32_rex_effect_step 0x12a486 0x41 0xc3 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12a489 [0x41, 0x69, 0xC3, 0x7B, 0x14, 0x00, 0x00] (fun s => s.RIP = 0x12a489) (imulR32R32Imm32Effect 0x12a489 7 0 11 0x147b)
      [.gpr 11] [] [.reg 0, .flags, .rip] :=
    (imulR32R32Imm32Effect_footprint 0x12a489 7 0 11 0x147b).toInstrSpec (imul_r32_r32_imm32_rex_effect_step 0x12a489 0x41 (by decide) 0xc3 (by decide) 0x147b) pre_rip
  have f8 : InstrSpec 0x12a490 [0xC1, 0xE8, 0x13] (fun s => s.RIP = 0x12a490) (shrR32Effect 0x12a490 3 0 19)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a490 3 0 19).toInstrSpec (shr_r32_imm8_effect_step 0x12a490 0xe8 0x13 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x12a493 [0x6B, 0xD8, 0x64] (fun s => s.RIP = 0x12a493) (imulR32R32Imm8Effect 0x12a493 3 3 0 0x64)
      [.gpr 0] [] [.reg 3, .flags, .rip] :=
    (imulR32R32Imm8Effect_footprint 0x12a493 3 3 0 0x64).toInstrSpec (imul_r32_r32_imm8_effect_step 0x12a493 0xd8 (by decide) 0x64) pre_rip
  have f10 : InstrSpec 0x12a496 [0x41, 0x29, 0xDB] (fun s => s.RIP = 0x12a496) (subR32R32Effect 0x12a496 3 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (subR32R32Effect_footprint 0x12a496 3 11 3).toInstrSpec (sub_r32_r32_rex_effect_step 0x12a496 0x41 0xdb (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12a499 [0x0F, 0xB7, 0x04, 0x47] (LoadPre 0x12a499 (fun s => AddrMode.addr (.sib 7 (some 0) 1 .none) s (0x12a499 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x12a499 4 0 (.sib 7 (some 0) 1 .none))
      [.gpr 7, .gpr 0] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x12a499 4 0 (.sib 7 (some 0) 1 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x12a499 0 (.sib 7 (some 0) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x12a49d [0x66, 0x42, 0x89, 0x44, 0x15, 0xE0] (StorePre 0x12a49d 6 (fun s => AddrMode.addr (.sib 5 (some 10) 0 (.d8 0xe0)) s (0x12a49d + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x12a49d 6 0 (.sib 5 (some 10) 0 (.d8 0xe0)))
      [.gpr 0, .gpr 5, .gpr 10] [] [.rip] :=
    (movM16R16Effect_footprint 0x12a49d 6 0 (.sib 5 (some 10) 0 (.d8 0xe0))).toInstrSpec (mov_m16_r16_rex_effect_step 0x12a49d 0x42 (by decide) 0 (.sib 5 (some 10) 0 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x12a4a3 [0x41, 0x0F, 0xB7, 0xC3] (fun s => s.RIP = 0x12a4a3) (movzxR32R16Effect 0x12a4a3 4 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movzxR32R16Effect_footprint 0x12a4a3 4 0 11).toInstrSpec (movzx_r32_r16_rex_effect_step 0x12a4a3 0x41 (by decide) 0xc3 (by decide)) pre_rip
  have f14 : InstrSpec 0x12a4a7 [0x0F, 0xB7, 0x04, 0x47] (LoadPre 0x12a4a7 (fun s => AddrMode.addr (.sib 7 (some 0) 1 .none) s (0x12a4a7 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x12a4a7 4 0 (.sib 7 (some 0) 1 .none))
      [.gpr 7, .gpr 0] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x12a4a7 4 0 (.sib 7 (some 0) 1 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x12a4a7 0 (.sib 7 (some 0) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x12a4ab [0x66, 0x42, 0x89, 0x44, 0x15, 0xE2] (StorePre 0x12a4ab 6 (fun s => AddrMode.addr (.sib 5 (some 10) 0 (.d8 0xe2)) s (0x12a4ab + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x12a4ab 6 0 (.sib 5 (some 10) 0 (.d8 0xe2)))
      [.gpr 0, .gpr 5, .gpr 10] [] [.rip] :=
    (movM16R16Effect_footprint 0x12a4ab 6 0 (.sib 5 (some 10) 0 (.d8 0xe2))).toInstrSpec (mov_m16_r16_rex_effect_step 0x12a4ab 0x42 (by decide) 0 (.sib 5 (some 10) 0 (.d8 0xe2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x12a4b1 [0x49, 0x8D, 0x42, 0xFC] (fun s => s.RIP = 0x12a4b1) (leaR64Effect 0x12a4b1 0 (.base 10 (.d8 0xfc)))
      [.gpr 10] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x12a4b1 0 (.base 10 (.d8 0xfc))).toInstrSpec (lea_r64_effect_step 0x12a4b1 0x49 (by decide) 0 (.base 10 (.d8 0xfc)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x12a4b5 [0x48, 0x81, 0xF9, 0x7F, 0x96, 0x98, 0x00] (fun s => s.RIP = 0x12a4b5) (cmpR64Imm32Effect 0x12a4b5 1 0x98967f)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm32Effect_footprint 0x12a4b5 1 0x98967f).toInstrSpec (cmp_r64_imm32_effect_step 0x12a4b5 0x48 0xf9 0x98967f (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x12a4bc [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x12a4bc) (movR64R64Effect 0x12a4bc 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a4bc 1 2).toInstrSpec (mov_r64_r64_effect_step 0x12a4bc 0x48 0xd1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a473) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a476) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a479) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a47d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a483) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a486) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a489) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a490) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a493) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a496) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 69), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a499) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a49d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4a3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4a7) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4ab) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 80), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4b1) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4b5) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f17 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 83), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (16, 85), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4bc) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 83), (1, 88), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (16, 85), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4bf) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 90) (jcc_rel8_effect_step 0x12a4bf 7 0xaf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a470 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a470 :=
  Rest.liftedBlock (rest_l12a470 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a470 x hx)

theorem rest_l12a4c1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a4c1 bytes_l12a4c1) (entryMap (live .l12a4c1))
      2 0x12a4c1 bytes_l12a4c1 b_l12a4c1 := by
  have f0 : InstrSpec 0x12a4c1 [0x48, 0x83, 0xFA, 0x09] (fun s => s.RIP = 0x12a4c1) (cmpR64Imm8Effect 0x12a4c1 2 0x9)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x12a4c1 2 0x9).toInstrSpec (cmp_r64_imm8_effect_step 0x12a4c1 0x48 0xfa 0x9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4c5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x12a4c5 6 0x2b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a4c1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a4c1 :=
  Rest.liftedBlock (rest_l12a4c1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a4c1 x hx)

theorem rest_l12a4c7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a4c7 bytes_l12a4c7) (entryMap (live .l12a4c7))
      12 0x12a4c7 bytes_l12a4c7 b_l12a4c7 := by
  have f0 : InstrSpec 0x12a4c7 [0x89, 0xD1] (fun s => s.RIP = 0x12a4c7) (movR32R32Effect 0x12a4c7 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x12a4c7 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x12a4c7 0xd1 (by decide)) pre_rip
  have f1 : InstrSpec 0x12a4c9 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x12a4c9) (shrR32Effect 0x12a4c9 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a4c9 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x12a4c9 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a4cc [0x0F, 0xB7, 0xC9] (fun s => s.RIP = 0x12a4cc) (movzxR32R16Effect 0x12a4cc 3 1 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movzxR32R16Effect_footprint 0x12a4cc 3 1 1).toInstrSpec (movzx_r32_r16_effect_step 0x12a4cc 0xc9 (by decide)) pre_rip
  have f3 : InstrSpec 0x12a4cf [0x69, 0xC9, 0x7B, 0x14, 0x00, 0x00] (fun s => s.RIP = 0x12a4cf) (imulR32R32Imm32Effect 0x12a4cf 6 1 1 0x147b)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (imulR32R32Imm32Effect_footprint 0x12a4cf 6 1 1 0x147b).toInstrSpec (imul_r32_r32_imm32_effect_step 0x12a4cf 0xc9 (by decide) 0x147b) pre_rip
  have f4 : InstrSpec 0x12a4d5 [0xC1, 0xE9, 0x11] (fun s => s.RIP = 0x12a4d5) (shrR32Effect 0x12a4d5 3 1 17)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a4d5 3 1 17).toInstrSpec (shr_r32_imm8_effect_step 0x12a4d5 0xe9 0x11 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12a4d8 [0x44, 0x6B, 0xC9, 0x64] (fun s => s.RIP = 0x12a4d8) (imulR32R32Imm8Effect 0x12a4d8 4 9 1 0x64)
      [.gpr 1] [] [.reg 9, .flags, .rip] :=
    (imulR32R32Imm8Effect_footprint 0x12a4d8 4 9 1 0x64).toInstrSpec (imul_r32_r32_imm8_rex_effect_step 0x12a4d8 0x44 (by decide) 0xc9 (by decide) 0x64) pre_rip
  have f6 : InstrSpec 0x12a4dc [0x44, 0x29, 0xCA] (fun s => s.RIP = 0x12a4dc) (subR32R32Effect 0x12a4dc 3 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (subR32R32Effect_footprint 0x12a4dc 3 2 9).toInstrSpec (sub_r32_r32_rex_effect_step 0x12a4dc 0x44 0xca (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12a4df [0x0F, 0xB7, 0xD2] (fun s => s.RIP = 0x12a4df) (movzxR32R16Effect 0x12a4df 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R16Effect_footprint 0x12a4df 3 2 2).toInstrSpec (movzx_r32_r16_effect_step 0x12a4df 0xd2 (by decide)) pre_rip
  have f8 : InstrSpec 0x12a4e2 [0x0F, 0xB7, 0x14, 0x57] (LoadPre 0x12a4e2 (fun s => AddrMode.addr (.sib 7 (some 2) 1 .none) s (0x12a4e2 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x12a4e2 4 2 (.sib 7 (some 2) 1 .none))
      [.gpr 7, .gpr 2] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x12a4e2 4 2 (.sib 7 (some 2) 1 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x12a4e2 2 (.sib 7 (some 2) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x12a4e6 [0x66, 0x89, 0x54, 0x05, 0xE2] (StorePre 0x12a4e6 5 (fun s => AddrMode.addr (.sib 5 (some 0) 0 (.d8 0xe2)) s (0x12a4e6 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x12a4e6 5 2 (.sib 5 (some 0) 0 (.d8 0xe2)))
      [.gpr 2, .gpr 5, .gpr 0] [] [.rip] :=
    (movM16R16Effect_footprint 0x12a4e6 5 2 (.sib 5 (some 0) 0 (.d8 0xe2))).toInstrSpec (mov_m16_r16_effect_step 0x12a4e6 2 (.sib 5 (some 0) 0 (.d8 0xe2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x12a4eb [0x48, 0x83, 0xC0, 0xFE] (fun s => s.RIP = 0x12a4eb) (addR64Imm8Effect 0x12a4eb 0 0xfe)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12a4eb 0 0xfe).toInstrSpec (add_r64_imm8_effect_step 0x12a4eb 0x48 0xc0 0xfe (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12a4ef [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x12a4ef) (movR64R64Effect 0x12a4ef 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12a4ef 2 1).toInstrSpec (mov_r64_r64_effect_step 0x12a4ef 0x48 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4c9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4cc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4cf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4d5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4d8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4dc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 61), (2, 65), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4df) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 61), (2, 67), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4e2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4e6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4eb) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4ef) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 72), (1, 61), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4f2) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 76) (by decide) rfl

theorem block_l12a4c7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a4c7 :=
  Rest.liftedBlock (rest_l12a4c7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a4c7 x hx)

theorem rest_l12a4f2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a4f2 bytes_l12a4f2) (entryMap (live .l12a4f2))
      2 0x12a4f2 bytes_l12a4f2 b_l12a4f2 := by
  have f0 : InstrSpec 0x12a4f2 [0x4D, 0x85, 0xC0] (fun s => s.RIP = 0x12a4f2) (testR64R64Effect 0x12a4f2 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x12a4f2 8 8).toInstrSpec (test_r64_r64_effect_step 0x12a4f2 0x4d 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4f5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12a4f5 4 0x5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a4f2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a4f2 :=
  Rest.liftedBlock (rest_l12a4f2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a4f2 x hx)

theorem rest_l12a4f7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a4f7 bytes_l12a4f7) (entryMap (live .l12a4f7))
      2 0x12a4f7 bytes_l12a4f7 b_l12a4f7 := by
  have f0 : InstrSpec 0x12a4f7 [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x12a4f7) (testR64R64Effect 0x12a4f7 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x12a4f7 2 2).toInstrSpec (test_r64_r64_effect_step 0x12a4f7 0x48 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4fa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12a4fa 4 0xc) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a4f7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a4f7 :=
  Rest.liftedBlock (rest_l12a4f7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a4f7 x hx)

theorem rest_l12a4fc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a4fc bytes_l12a4fc) (entryMap (live .l12a4fc))
      3 0x12a4fc bytes_l12a4fc b_l12a4fc := by
  have f0 : InstrSpec 0x12a4fc [0x0F, 0xB6, 0x4C, 0x57, 0x01] (LoadPre 0x12a4fc (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x1)) s (0x12a4fc + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x12a4fc 5 1 (.sib 7 (some 2) 1 (.d8 0x1)))
      [.gpr 7, .gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x12a4fc 5 1 (.sib 7 (some 2) 1 (.d8 0x1))).toInstrSpec (movzx_r32_m8_effect_step 0x12a4fc 1 (.sib 7 (some 2) 1 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12a501 [0x88, 0x4C, 0x05, 0xE3] (StorePre 0x12a501 4 (fun s => AddrMode.addr (.sib 5 (some 0) 0 (.d8 0xe3)) s (0x12a501 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x12a501 4 1 (.sib 5 (some 0) 0 (.d8 0xe3)))
      [.gpr 1, .gpr 5, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x12a501 4 1 (.sib 5 (some 0) 0 (.d8 0xe3))).toInstrSpec (mov_m8_r8_effect_step 0x12a501 1 (by decide) (.sib 5 (some 0) 0 (.d8 0xe3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12a505 [0x48, 0xFF, 0xC8] (fun s => s.RIP = 0x12a505) (decR64Effect 0x12a505 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (decR64Effect_footprint 0x12a505 0).toInstrSpec (dec_r64_effect_step 0x12a505 0x48 0xc8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a501) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a505) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a508) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l12a4fc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a4fc :=
  Rest.liftedBlock (rest_l12a4fc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a4fc x hx)

theorem rest_l12a508 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a508 bytes_l12a508) (entryMap (live .l12a508))
      9 0x12a508 bytes_l12a508 b_l12a508 := by
  have f0 : InstrSpec 0x12a508 [0x41, 0xB9, 0x14, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a508) (movR32Imm32Effect 0x12a508 6 9 0x14)
      [] [] [.reg 9, .rip] :=
    (movR32Imm32Effect_footprint 0x12a508 6 9 0x14).toInstrSpec (mov_r32_imm32_rex_effect_step 0x12a508 0x41 0xb9 (by decide) (by decide) 0x14) pre_rip
  have f1 : InstrSpec 0x12a50e [0x49, 0x29, 0xC1] (fun s => s.RIP = 0x12a50e) (subR64R64Effect 0x12a50e 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x12a50e 9 0).toInstrSpec (sub_r64_r64_effect_step 0x12a50e 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a511 [0x4C, 0x8D, 0x04, 0x28] (fun s => s.RIP = 0x12a511) (leaR64Effect 0x12a511 8 (.sib 0 (some 5) 0 .none))
      [.gpr 0, .gpr 5] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x12a511 8 (.sib 0 (some 5) 0 .none)).toInstrSpec (lea_r64_effect_step 0x12a511 0x4c (by decide) 0 (.sib 0 (some 5) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12a515 [0x49, 0x83, 0xC0, 0xE4] (fun s => s.RIP = 0x12a515) (addR64Imm8Effect 0x12a515 8 0xe4)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12a515 8 0xe4).toInstrSpec (add_r64_imm8_effect_step 0x12a515 0x49 0xc0 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a519 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a519) (movR32Imm32Effect 0x12a519 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x12a519 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x12a519 0xba (by decide) 0x1) pre_rip
  have f5 : InstrSpec 0x12a51e [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x12a51e) (movR64R64Effect 0x12a51e 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12a51e 7 6).toInstrSpec (mov_r64_r64_effect_step 0x12a51e 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12a521 [0xBE, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a521) (movR32Imm32Effect 0x12a521 5 6 0x1)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x12a521 5 6 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x12a521 0xbe (by decide) 0x1) pre_rip
  have f7 : InstrSpec 0x12a526 [0x31, 0xC9] (fun s => s.RIP = 0x12a526) (xorR32R32Effect 0x12a526 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12a526 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x12a526 0xc9 (by decide)) pre_rip
  have f8 : InstrSpec 0x12a528 [0xFF, 0x15, 0xBA, 0x98, 0x0D, 0x00] (GoesTo (CallMemPre 0x12a528 (.rip 0xd98ba)) (callEffect (callMemPtr 0x12a528 (.rip 0xd98ba)) (0x12a528 + BitVec.ofNat 64 (callMemLen (.rip 0xd98ba)))) 0x128b20) (callEffect (callMemPtr 0x12a528 (.rip 0xd98ba)) (0x12a528 + BitVec.ofNat 64 (callMemLen (.rip 0xd98ba))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x12a528 (.rip 0xd98ba)).toInstrSpec (call_m64_effect_step 0x12a528 (.rip 0xd98ba) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x128b20
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a50e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a511) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 57), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a515) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a519) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a51e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a521) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a526) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 61), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a528) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 67), (2, 61), (3, 3), (4, 69), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b20) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l12a508 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a508 :=
  Rest.liftedBlock (rest_l12a508 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a508 x hx)

theorem rest_l12a52e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a52e bytes_l12a52e) (entryMap (live .l12a52e))
      4 0x12a52e bytes_l12a52e b_l12a52e := by
  have f0 : InstrSpec 0x12a52e [0x48, 0x83, 0xC4, 0x18] (fun s => s.RIP = 0x12a52e) (addR64Imm8Effect 0x12a52e 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12a52e 4 0x18).toInstrSpec (add_r64_imm8_effect_step 0x12a52e 0x48 0xc4 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a532 [0x5B] (PopPre 0x12a532) (popR64Effect 0x12a532 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12a532 1 3).toInstrSpec (pop_r64_effect_step 0x12a532 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x12a533 [0x5D] (PopPre 0x12a533) (popR64Effect 0x12a533 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12a533 1 5).toInstrSpec (pop_r64_effect_step 0x12a533 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x12a534 [0xC3] (RetPre 0x12a534) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12a534).toInstrSpec (ret_effect_step 0x12a534) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a532) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a533) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (5, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a534) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (5, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f3 (by decide) rfl rfl rfl (by decide)

theorem block_l12a52e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a52e :=
  Rest.liftedBlock (rest_l12a52e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a52e x hx)

theorem rest_l12a700_1 [Bindings] (code : CodeMap) :
    Rest (n := 94) code lifted (codeRange 0x12a700 bytes_l12a700) [(0, 92), (1, 90), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x12a744 bytes_l12a700_1 b_l12a700_1 := by
  have f20 : InstrSpec 0x12a744 [0xC3] (RetPre 0x12a744) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12a744).toInstrSpec (ret_effect_step 0x12a744) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f20 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 95) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 96) (ρ' := [(0, 92), (1, 90), (2, 55), (3, 3), (4, 95), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f20 (by decide) rfl rfl rfl (by decide)

theorem rest_l12a700 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a700 bytes_l12a700) (entryMap (live .l12a700))
      21 0x12a700 bytes_l12a700 b_l12a700 := by
  have f0 : InstrSpec 0x12a700 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x12a700) (movR64R64Effect 0x12a700 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x12a700 8 2).toInstrSpec (mov_r64_r64_effect_step 0x12a700 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a703 [0x48, 0x89, 0xFA] (fun s => s.RIP = 0x12a703) (movR64R64Effect 0x12a703 2 7)
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12a703 2 7).toInstrSpec (mov_r64_r64_effect_step 0x12a703 0x48 0xfa (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a706 [0x40, 0x0F, 0xB6, 0xCE] (fun s => s.RIP = 0x12a706) (movzxR32R8Effect 0x12a706 4 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x12a706 4 1 6).toInstrSpec (movzx_r32_r8_rex_effect_step 0x12a706 0x40 (by decide) 0xce (by decide)) pre_rip
  have f3 : InstrSpec 0x12a70a [0x48, 0xB8, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01] (fun s => s.RIP = 0x12a70a) (movR64Imm64Effect 0x12a70a 0 0x101010101010101)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x12a70a 0 0x101010101010101).toInstrSpec (mov_r64_imm64_effect_step 0x12a70a 0x48 0xb8 (by decide) (by decide) 0x101010101010101) pre_rip
  have f4 : InstrSpec 0x12a714 [0x48, 0x0F, 0xAF, 0xC1] (fun s => s.RIP = 0x12a714) (imulR64R64Effect 0x12a714 4 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x12a714 4 0 1).toInstrSpec (imul_r64_r64_effect_step 0x12a714 0x48 (by decide) 0xc1 (by decide)) pre_rip
  have f5 : InstrSpec 0x12a718 [0x89, 0xD1] (fun s => s.RIP = 0x12a718) (movR32R32Effect 0x12a718 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x12a718 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x12a718 0xd1 (by decide)) pre_rip
  have f6 : InstrSpec 0x12a71a [0xF7, 0xD9] (fun s => s.RIP = 0x12a71a) (negR32Effect 0x12a71a 2 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR32Effect_footprint 0x12a71a 2 1).toInstrSpec (neg_r32_effect_step 0x12a71a 0xd9 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12a71c [0x83, 0xE1, 0x07] (fun s => s.RIP = 0x12a71c) (andR32Imm8Effect 0x12a71c 3 1 0x7)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x12a71c 3 1 0x7).toInstrSpec (and_r32_imm8_effect_step 0x12a71c 0xe1 0x7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12a71f [0x49, 0x39, 0xC8] (fun s => s.RIP = 0x12a71f) (cmpR64R64Effect 0x12a71f 8 1)
      [.gpr 8, .gpr 1] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12a71f 8 1).toInstrSpec (cmp_r64_r64_effect_step 0x12a71f 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x12a722 [0x49, 0x0F, 0x42, 0xC8] (fun s => s.RIP = 0x12a722) (atFlags (condHolds 2) (cmovR64R64Effect 0x12a722 4 1 8))
      [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .rip] :=
    (cmovR64R64Effect_footprint 0x12a722 4 1 8 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x12a722 2 0x49 (by decide) 0xc8 (by decide) c)) pre_rip
  have f10 : InstrSpec 0x12a726 [0x49, 0x29, 0xC8] (fun s => s.RIP = 0x12a726) (subR64R64Effect 0x12a726 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (subR64R64Effect_footprint 0x12a726 8 1).toInstrSpec (sub_r64_r64_effect_step 0x12a726 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12a729 [0x4C, 0x89, 0xC6] (fun s => s.RIP = 0x12a729) (movR64R64Effect 0x12a729 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12a729 6 8).toInstrSpec (mov_r64_r64_effect_step 0x12a729 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x12a72c [0x48, 0xC1, 0xEE, 0x03] (fun s => s.RIP = 0x12a72c) (shrR64Effect 0x12a72c 4 6 3)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x12a72c 4 6 3).toInstrSpec (shr_r64_imm8_effect_step 0x12a72c 0x48 0xee 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x12a730 [0x41, 0x83, 0xE0, 0x07] (fun s => s.RIP = 0x12a730) (andR32Imm8Effect 0x12a730 4 8 0x7)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x12a730 4 8 0x7).toInstrSpec (and_r32_imm8_rex_effect_step 0x12a730 0x41 0xe0 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x12a734 [0xF3, 0xAA] (RepPre 0x12a734 (RepStosbPre 0x12a734)) (repStosbEffect 0x12a734)
      [.gpr 0, .gpr 7, .gpr 1, .df] [] [.reg 7, .reg 1, .rip] :=
    (repStosbEffect_footprint 0x12a734).toInstrSpecOfRuns (rep_stosb_runs hstride 0x12a734) (RepStosOk.of_stateOf RepStosbPre.iff (by lift_reads) (by lift_reads) (by lift_reads))
  have f15 : InstrSpec 0x12a736 [0x48, 0x89, 0xF1] (fun s => s.RIP = 0x12a736) (movR64R64Effect 0x12a736 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a736 1 6).toInstrSpec (mov_r64_r64_effect_step 0x12a736 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x12a739 [0xF3, 0x48, 0xAB] (RepPre 0x12a739 (RepStosqPre 0x12a739)) (repStosqEffect 0x12a739)
      [.gpr 0, .gpr 7, .gpr 1, .df] [] [.reg 7, .reg 1, .rip] :=
    (repStosqEffect_footprint 0x12a739).toInstrSpecOfRuns (rep_stosq_runs hstride 0x12a739 0x48 (by decide)) (RepStosOk.of_stateOf RepStosqPre.iff (by lift_reads) (by lift_reads) (by lift_reads))
  have f17 : InstrSpec 0x12a73c [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x12a73c) (movR64R64Effect 0x12a73c 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a73c 1 8).toInstrSpec (mov_r64_r64_effect_step 0x12a73c 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x12a73f [0xF3, 0xAA] (RepPre 0x12a73f (RepStosbPre 0x12a73f)) (repStosbEffect 0x12a73f)
      [.gpr 0, .gpr 7, .gpr 1, .df] [] [.reg 7, .reg 1, .rip] :=
    (repStosbEffect_footprint 0x12a73f).toInstrSpecOfRuns (rep_stosb_runs hstride 0x12a73f) (RepStosOk.of_stateOf RepStosbPre.iff (by lift_reads) (by lift_reads) (by lift_reads))
  have f19 : InstrSpec 0x12a741 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x12a741) (movR64R64Effect 0x12a741 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12a741 0 2).toInstrSpec (mov_r64_r64_effect_step 0x12a741 0x48 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a703) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a706) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a70a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a714) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a718) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a71a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 65), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a71c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 67), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a71f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 61), (1, 67), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a722) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a726) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 73), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a729) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 75), (7, 7), (8, 73), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a72c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 7), (8, 73), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a730) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 7), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a734) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 81), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a736) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 61), (1, 83), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 81), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a739) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 85), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a73c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 61), (1, 87), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 85), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a73f) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 90) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 91) (ρ' := [(0, 61), (1, 90), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a741) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 92), (1, 90), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a744) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12a700_1 code

theorem block_l12a700 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a700 :=
  Rest.liftedBlock (rest_l12a700 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a700 x hx)

theorem rest_l12a750 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a750 bytes_l12a750) (entryMap (live .l12a750))
      13 0x12a750 bytes_l12a750 b_l12a750 := by
  have f0 : InstrSpec 0x12a750 [0x55] (PushPre 0x12a750 1) (pushR64Effect 0x12a750 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12a750 1 5).toInstrSpec (push_r64_effect_step 0x12a750 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x12a751 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x12a751) (movR64R64Effect 0x12a751 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x12a751 5 4).toInstrSpec (mov_r64_r64_effect_step 0x12a751 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a754 [0x41, 0x57] (PushPre 0x12a754 2) (pushR64Effect 0x12a754 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12a754 2 15).toInstrSpec (push_r64_rex_effect_step 0x12a754 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x12a756 [0x41, 0x56] (PushPre 0x12a756 2) (pushR64Effect 0x12a756 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12a756 2 14).toInstrSpec (push_r64_rex_effect_step 0x12a756 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x12a758 [0x41, 0x54] (PushPre 0x12a758 2) (pushR64Effect 0x12a758 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12a758 2 12).toInstrSpec (push_r64_rex_effect_step 0x12a758 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x12a75a [0x53] (PushPre 0x12a75a 1) (pushR64Effect 0x12a75a 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12a75a 1 3).toInstrSpec (push_r64_effect_step 0x12a75a 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x12a75b [0x48, 0x83, 0xEC, 0x10] (fun s => s.RIP = 0x12a75b) (subR64Imm8Effect 0x12a75b 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x12a75b 4 0x10).toInstrSpec (sub_r64_imm8_effect_step 0x12a75b 0x48 0xec 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12a75f [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x12a75f) (movR64R64Effect 0x12a75f 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a75f 1 2).toInstrSpec (mov_r64_r64_effect_step 0x12a75f 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12a762 [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x12a762) (movR64R64Effect 0x12a762 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12a762 2 6).toInstrSpec (mov_r64_r64_effect_step 0x12a762 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x12a765 [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x12a765) (movR64R64Effect 0x12a765 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12a765 6 7).toInstrSpec (mov_r64_r64_effect_step 0x12a765 0x48 0xfe (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x12a768 [0x49, 0x89, 0xC8] (fun s => s.RIP = 0x12a768) (movR64R64Effect 0x12a768 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x12a768 8 1).toInstrSpec (mov_r64_r64_effect_step 0x12a768 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12a76b [0x49, 0x83, 0xE0, 0xF0] (fun s => s.RIP = 0x12a76b) (andR64Imm8Effect 0x12a76b 8 0xf0)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x12a76b 8 0xf0).toInstrSpec (and_r64_imm8_effect_step 0x12a76b 0x49 0xe0 0xf0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a751) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a754) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a756) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a758) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a75a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a75b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a75f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 67), (2, 2), (3, 3), (4, 65), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a762) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a765) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 55), (6, 71), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a768) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 55), (6, 71), (7, 7), (8, 73), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a76b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 77) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 55), (6, 71), (7, 7), (8, 75), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a76f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 78) (jcc_rel8_effect_step 0x12a76f 4 0x41) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a750 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a750 :=
  Rest.liftedBlock (rest_l12a750 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a750 x hx)

theorem rest_l12a771 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a771 bytes_l12a771) (entryMap (live .l12a771))
      4 0x12a771 bytes_l12a771 b_l12a771 := by
  have f0 : InstrSpec 0x12a771 [0x4E, 0x8D, 0x0C, 0x06] (fun s => s.RIP = 0x12a771) (leaR64Effect 0x12a771 9 (.sib 6 (some 8) 0 .none))
      [.gpr 6, .gpr 8] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x12a771 9 (.sib 6 (some 8) 0 .none)).toInstrSpec (lea_r64_effect_step 0x12a771 0x4e (by decide) 1 (.sib 6 (some 8) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a775 [0x4E, 0x8D, 0x14, 0x02] (fun s => s.RIP = 0x12a775) (leaR64Effect 0x12a775 10 (.sib 2 (some 8) 0 .none))
      [.gpr 2, .gpr 8] [] [.reg 10, .rip] :=
    (leaR64Effect_footprint 0x12a775 10 (.sib 2 (some 8) 0 .none)).toInstrSpec (lea_r64_effect_step 0x12a775 0x4e (by decide) 2 (.sib 2 (some 8) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a779 [0x45, 0x31, 0xDB] (fun s => s.RIP = 0x12a779) (xorR32R32Effect 0x12a779 3 11 11)
      [.gpr 11, .gpr 11] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12a779 3 11 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x12a779 0x45 0xdb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12a77c [0x0F, 0x1F, 0x40, 0x00] (fun s => s.RIP = 0x12a77c) (fun _ => nopEffect 0x12a77c 4)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12a77c 4).toInstrSpec (nop_m_effect_step 0x12a77c [] (by decide) (by decide) (.base 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 53), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a775) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 53), (10, 55), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a779) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 53), (10, 55), (11, 57), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a77c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 53), (10, 55), (11, 57), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a780) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l12a771 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a771 :=
  Rest.liftedBlock (rest_l12a771 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a771 x hx)

theorem rest_l12a780 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a780 bytes_l12a780) (entryMap (live .l12a780))
      10 0x12a780 bytes_l12a780 b_l12a780 := by
  have f0 : InstrSpec 0x12a780 [0x4A, 0x8B, 0x04, 0x1E] (LoadPre 0x12a780 (fun s => AddrMode.addr (.sib 6 (some 11) 0 .none) s (0x12a780 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a780 0 (.sib 6 (some 11) 0 .none))
      [.gpr 6, .gpr 11] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12a780 0 (.sib 6 (some 11) 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a780 0x4a (by decide) 0 (.sib 6 (some 11) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12a784 [0x4A, 0x8B, 0x5C, 0x1E, 0x08] (LoadPre 0x12a784 (fun s => AddrMode.addr (.sib 6 (some 11) 0 (.d8 0x8)) s (0x12a784 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12a784 3 (.sib 6 (some 11) 0 (.d8 0x8)))
      [.gpr 6, .gpr 11] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x12a784 3 (.sib 6 (some 11) 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12a784 0x4a (by decide) 3 (.sib 6 (some 11) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12a789 [0x4A, 0x8B, 0x3C, 0x1A] (LoadPre 0x12a789 (fun s => AddrMode.addr (.sib 2 (some 11) 0 .none) s (0x12a789 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a789 7 (.sib 2 (some 11) 0 .none))
      [.gpr 2, .gpr 11] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12a789 7 (.sib 2 (some 11) 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a789 0x4a (by decide) 7 (.sib 2 (some 11) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12a78d [0x4E, 0x8B, 0x74, 0x1A, 0x08] (LoadPre 0x12a78d (fun s => AddrMode.addr (.sib 2 (some 11) 0 (.d8 0x8)) s (0x12a78d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12a78d 14 (.sib 2 (some 11) 0 (.d8 0x8)))
      [.gpr 2, .gpr 11] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x12a78d 14 (.sib 2 (some 11) 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12a78d 0x4e (by decide) 6 (.sib 2 (some 11) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x12a792 [0x49, 0x89, 0xDF] (fun s => s.RIP = 0x12a792) (movR64R64Effect 0x12a792 15 3)
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x12a792 15 3).toInstrSpec (mov_r64_r64_effect_step 0x12a792 0x49 0xdf (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12a795 [0x4D, 0x31, 0xF7] (fun s => s.RIP = 0x12a795) (xorR64R64Effect 0x12a795 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x12a795 15 14).toInstrSpec (xor_r64_r64_effect_step 0x12a795 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12a798 [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x12a798) (movR64R64Effect 0x12a798 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x12a798 12 0).toInstrSpec (mov_r64_r64_effect_step 0x12a798 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12a79b [0x49, 0x31, 0xFC] (fun s => s.RIP = 0x12a79b) (xorR64R64Effect 0x12a79b 12 7)
      [.gpr 12, .gpr 7] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x12a79b 12 7).toInstrSpec (xor_r64_r64_effect_step 0x12a79b 0x49 0xfc (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12a79e [0x4D, 0x09, 0xFC] (fun s => s.RIP = 0x12a79e) (orR64R64Effect 0x12a79e 12 15)
      [.gpr 12, .gpr 15] [] [.reg 12, .flags, .rip] :=
    (orR64R64Effect_footprint 0x12a79e 12 15).toInstrSpec (or_r64_r64_effect_step 0x12a79e 0x4d 0xfc (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a784) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a789) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a78d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a792) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 59), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a795) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 59), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a798) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 59), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a79b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (13, 13), (14, 59), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a79e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 13), (14, 59), (15, 63), (19, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7a1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 72) (jcc_rel8_effect_step 0x12a7a1 5 0x1d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a780 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a780 :=
  Rest.liftedBlock (rest_l12a780 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a780 x hx)

theorem rest_l12a7a3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a7a3 bytes_l12a7a3) (entryMap (live .l12a7a3))
      3 0x12a7a3 bytes_l12a7a3 b_l12a7a3 := by
  have f0 : InstrSpec 0x12a7a3 [0x49, 0x83, 0xC3, 0x10] (fun s => s.RIP = 0x12a7a3) (addR64Imm8Effect 0x12a7a3 11 0x10)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12a7a3 11 0x10).toInstrSpec (add_r64_imm8_effect_step 0x12a7a3 0x49 0xc3 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a7a7 [0x4D, 0x39, 0xD8] (fun s => s.RIP = 0x12a7a7) (cmpR64R64Effect 0x12a7a7 8 11)
      [.gpr 8, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12a7a7 8 11).toInstrSpec (cmp_r64_r64_effect_step 0x12a7a7 0x4d 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7a7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7aa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x12a7aa 5 0xd4) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a7a3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a7a3 :=
  Rest.liftedBlock (rest_l12a7a3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a7a3 x hx)

theorem rest_l12a7ac [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a7ac bytes_l12a7ac) (entryMap (live .l12a7ac))
      2 0x12a7ac bytes_l12a7ac b_l12a7ac := by
  have f0 : InstrSpec 0x12a7ac [0x4C, 0x89, 0xD2] (fun s => s.RIP = 0x12a7ac) (movR64R64Effect 0x12a7ac 2 10)
      [.gpr 10] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12a7ac 2 10).toInstrSpec (mov_r64_r64_effect_step 0x12a7ac 0x4c 0xd2 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a7af [0x4C, 0x89, 0xCE] (fun s => s.RIP = 0x12a7af) (movR64R64Effect 0x12a7af 6 9)
      [.gpr 9] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12a7af 6 9).toInstrSpec (mov_r64_r64_effect_step 0x12a7af 0x4c 0xce (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7af) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7b2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l12a7ac [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a7ac :=
  Rest.liftedBlock (rest_l12a7ac code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a7ac x hx)

theorem rest_l12a7b2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a7b2 bytes_l12a7b2) (entryMap (live .l12a7b2))
      3 0x12a7b2 bytes_l12a7b2 b_l12a7b2 := by
  have f0 : InstrSpec 0x12a7b2 [0x83, 0xE1, 0x0F] (fun s => s.RIP = 0x12a7b2) (andR32Imm8Effect 0x12a7b2 3 1 0xf)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x12a7b2 3 1 0xf).toInstrSpec (and_r32_imm8_effect_step 0x12a7b2 0xe1 0xf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a7b5 [0x48, 0x8D, 0x7D, 0xD8] (fun s => s.RIP = 0x12a7b5) (leaR64Effect 0x12a7b5 7 (.base 5 (.d8 0xd8)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x12a7b5 7 (.base 5 (.d8 0xd8))).toInstrSpec (lea_r64_effect_step 0x12a7b5 0x48 (by decide) 7 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a7b9 [0xE8, 0x92, 0x00, 0x00, 0x00] (PushPre 0x12a7b9 5) (callEffect (fun _ => 0x12a850) 0x12a7be)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12a7b9 0x12a850 0x12a7be).toInstrSpec (call_rel32_effect_step 0x12a7b9 0x92 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7b5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7b9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a850) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l12a7b2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a7b2 :=
  Rest.liftedBlock (rest_l12a7b2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a7b2 x hx)

theorem rest_l12a7be [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a7be bytes_l12a7be) (entryMap (live .l12a7be))
      1 0x12a7be bytes_l12a7be b_l12a7be := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x12a7be 0x53 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12a7be [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a7be :=
  Rest.liftedBlock (rest_l12a7be code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a7be x hx)

theorem rest_l12a7c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a7c0 bytes_l12a7c0) (entryMap (live .l12a7c0))
      2 0x12a7c0 bytes_l12a7c0 b_l12a7c0 := by
  have f0 : InstrSpec 0x12a7c0 [0x48, 0x39, 0xF8] (fun s => s.RIP = 0x12a7c0) (cmpR64R64Effect 0x12a7c0 0 7)
      [.gpr 0, .gpr 7] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12a7c0 0 7).toInstrSpec (cmp_r64_r64_effect_step 0x12a7c0 0x48 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7c3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12a7c3 5 0xb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a7c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a7c0 :=
  Rest.liftedBlock (rest_l12a7c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a7c0 x hx)

theorem rest_l12a7c5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a7c5 bytes_l12a7c5) (entryMap (live .l12a7c5))
      2 0x12a7c5 bytes_l12a7c5 b_l12a7c5 := by
  have f0 : InstrSpec 0x12a7c5 [0x4C, 0x39, 0xF3] (fun s => s.RIP = 0x12a7c5) (cmpR64R64Effect 0x12a7c5 3 14)
      [.gpr 3, .gpr 14] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12a7c5 3 14).toInstrSpec (cmp_r64_r64_effect_step 0x12a7c5 0x4c 0xf3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7c8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12a7c8 4 0x3c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a7c5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a7c5 :=
  Rest.liftedBlock (rest_l12a7c5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a7c5 x hx)

theorem rest_l12a7ca [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a7ca bytes_l12a7ca) (entryMap (live .l12a7ca))
      2 0x12a7ca bytes_l12a7ca b_l12a7ca := by
  have f0 : InstrSpec 0x12a7ca [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x12a7ca) (movR64R64Effect 0x12a7ca 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12a7ca 0 3).toInstrSpec (mov_r64_r64_effect_step 0x12a7ca 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a7cd [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x12a7cd) (movR64R64Effect 0x12a7cd 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12a7cd 7 14).toInstrSpec (mov_r64_r64_effect_step 0x12a7cd 0x4c 0xf7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7cd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7d0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l12a7ca [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a7ca :=
  Rest.liftedBlock (rest_l12a7ca code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a7ca x hx)

theorem rest_l12a7d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a7d0 bytes_l12a7d0) (entryMap (live .l12a7d0))
      2 0x12a7d0 bytes_l12a7d0 b_l12a7d0 := by
  have f0 : InstrSpec 0x12a7d0 [0x39, 0xF8] (fun s => s.RIP = 0x12a7d0) (cmpR32R32Effect 0x12a7d0 2 0 7)
      [.gpr 0, .gpr 7] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x12a7d0 2 0 7).toInstrSpec (cmp_r32_r32_effect_step 0x12a7d0 0xf8 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7d2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12a7d2 5 0xd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a7d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a7d0 :=
  Rest.liftedBlock (rest_l12a7d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a7d0 x hx)

theorem rest_l12a7d4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a7d4 bytes_l12a7d4) (entryMap (live .l12a7d4))
      4 0x12a7d4 bytes_l12a7d4 b_l12a7d4 := by
  have f0 : InstrSpec 0x12a7d4 [0x48, 0xC1, 0xEF, 0x20] (fun s => s.RIP = 0x12a7d4) (shrR64Effect 0x12a7d4 4 7 32)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x12a7d4 4 7 32).toInstrSpec (shr_r64_imm8_effect_step 0x12a7d4 0x48 0xef 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a7d8 [0x48, 0xC1, 0xE8, 0x20] (fun s => s.RIP = 0x12a7d8) (shrR64Effect 0x12a7d8 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x12a7d8 4 0 32).toInstrSpec (shr_r64_imm8_effect_step 0x12a7d8 0x48 0xe8 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a7dc [0x48, 0x39, 0xF8] (fun s => s.RIP = 0x12a7dc) (cmpR64R64Effect 0x12a7dc 0 7)
      [.gpr 0, .gpr 7] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12a7dc 0 7).toInstrSpec (cmp_r64_r64_effect_step 0x12a7dc 0x48 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7d8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7dc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7df) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x12a7df 4 0x25) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a7d4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a7d4 :=
  Rest.liftedBlock (rest_l12a7d4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a7d4 x hx)

theorem rest_l12a7e1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a7e1 bytes_l12a7e1) (entryMap (live .l12a7e1))
      2 0x12a7e1 bytes_l12a7e1 b_l12a7e1 := by
  have f0 : InstrSpec 0x12a7e1 [0x66, 0x39, 0xF8] (fun s => s.RIP = 0x12a7e1) (cmpR16R16Effect 0x12a7e1 3 0 7)
      [.gpr 0, .gpr 7] [] [.flags, .rip] :=
    (cmpR16R16Effect_footprint 0x12a7e1 3 0 7).toInstrSpec (cmp_r16_r16_effect_step 0x12a7e1 0xf8 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7e4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12a7e4 5 0xa) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a7e1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a7e1 :=
  Rest.liftedBlock (rest_l12a7e1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a7e1 x hx)

theorem rest_l12a7e6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a7e6 bytes_l12a7e6) (entryMap (live .l12a7e6))
      4 0x12a7e6 bytes_l12a7e6 b_l12a7e6 := by
  have f0 : InstrSpec 0x12a7e6 [0xC1, 0xEF, 0x10] (fun s => s.RIP = 0x12a7e6) (shrR32Effect 0x12a7e6 3 7 16)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a7e6 3 7 16).toInstrSpec (shr_r32_imm8_effect_step 0x12a7e6 0xef 0x10 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a7e9 [0xC1, 0xE8, 0x10] (fun s => s.RIP = 0x12a7e9) (shrR32Effect 0x12a7e9 3 0 16)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a7e9 3 0 16).toInstrSpec (shr_r32_imm8_effect_step 0x12a7e9 0xe8 0x10 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a7ec [0x39, 0xF8] (fun s => s.RIP = 0x12a7ec) (cmpR32R32Effect 0x12a7ec 2 0 7)
      [.gpr 0, .gpr 7] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x12a7ec 2 0 7).toInstrSpec (cmp_r32_r32_effect_step 0x12a7ec 0xf8 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7e9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7ec) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7ee) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x12a7ee 4 0x16) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a7e6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a7e6 :=
  Rest.liftedBlock (rest_l12a7e6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a7e6 x hx)

theorem rest_l12a7f0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a7f0 bytes_l12a7f0) (entryMap (live .l12a7f0))
      2 0x12a7f0 bytes_l12a7f0 b_l12a7f0 := by
  have f0 : InstrSpec 0x12a7f0 [0x40, 0x38, 0xF8] (fun s => s.RIP = 0x12a7f0) (cmpR8R8Effect 0x12a7f0 3 0 7)
      [.gpr 0, .gpr 7] [] [.flags, .rip] :=
    (cmpR8R8Effect_footprint 0x12a7f0 3 0 7).toInstrSpec (cmp_r8_r8_rex_effect_step 0x12a7f0 0x40 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7f3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12a7f3 5 0x15) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a7f0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a7f0 :=
  Rest.liftedBlock (rest_l12a7f0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a7f0 x hx)

theorem rest_l12a7f5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a7f5 bytes_l12a7f5) (entryMap (live .l12a7f5))
      6 0x12a7f5 bytes_l12a7f5 b_l12a7f5 := by
  have f0 : InstrSpec 0x12a7f5 [0x0F, 0xB7, 0xFF] (fun s => s.RIP = 0x12a7f5) (movzxR32R16Effect 0x12a7f5 3 7 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (movzxR32R16Effect_footprint 0x12a7f5 3 7 7).toInstrSpec (movzx_r32_r16_effect_step 0x12a7f5 0xff (by decide)) pre_rip
  have f1 : InstrSpec 0x12a7f8 [0xC1, 0xEF, 0x08] (fun s => s.RIP = 0x12a7f8) (shrR32Effect 0x12a7f8 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a7f8 3 7 8).toInstrSpec (shr_r32_imm8_effect_step 0x12a7f8 0xef 0x8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a7fb [0x0F, 0xB7, 0xC0] (fun s => s.RIP = 0x12a7fb) (movzxR32R16Effect 0x12a7fb 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R16Effect_footprint 0x12a7fb 3 0 0).toInstrSpec (movzx_r32_r16_effect_step 0x12a7fb 0xc0 (by decide)) pre_rip
  have f3 : InstrSpec 0x12a7fe [0xC1, 0xE8, 0x08] (fun s => s.RIP = 0x12a7fe) (shrR32Effect 0x12a7fe 3 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a7fe 3 0 8).toInstrSpec (shr_r32_imm8_effect_step 0x12a7fe 0xe8 0x8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a801 [0x66, 0x39, 0xF8] (fun s => s.RIP = 0x12a801) (cmpR16R16Effect 0x12a801 3 0 7)
      [.gpr 0, .gpr 7] [] [.flags, .rip] :=
    (cmpR16R16Effect_footprint 0x12a801 3 0 7).toInstrSpec (cmp_r16_r16_effect_step 0x12a801 0xf8 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7f8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7fb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (4, 4), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a7fe) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (4, 4), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a801) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 1), (2, 2), (4, 4), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a804) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x12a804 5 0x4) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a7f5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a7f5 :=
  Rest.liftedBlock (rest_l12a7f5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a7f5 x hx)

theorem rest_l12a806 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a806 bytes_l12a806) (entryMap (live .l12a806))
      2 0x12a806 bytes_l12a806 b_l12a806 := by
  have f0 : InstrSpec 0x12a806 [0x31, 0xC0] (fun s => s.RIP = 0x12a806) (xorR32R32Effect 0x12a806 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12a806 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x12a806 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a808) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x12a808 0x9 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12a806 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a806 :=
  Rest.liftedBlock (rest_l12a806 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a806 x hx)

theorem rest_l12a80a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a80a bytes_l12a80a) (entryMap (live .l12a80a))
      3 0x12a80a bytes_l12a80a b_l12a80a := by
  have f0 : InstrSpec 0x12a80a [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x12a80a) (movzxR32R8Effect 0x12a80a 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x12a80a 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x12a80a 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a80d [0x40, 0x0F, 0xB6, 0xCF] (fun s => s.RIP = 0x12a80d) (movzxR32R8Effect 0x12a80d 4 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x12a80d 4 1 7).toInstrSpec (movzx_r32_r8_rex_effect_step 0x12a80d 0x40 (by decide) 0xcf (by decide)) pre_rip
  have f2 : InstrSpec 0x12a811 [0x29, 0xC8] (fun s => s.RIP = 0x12a811) (subR32R32Effect 0x12a811 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (subR32R32Effect_footprint 0x12a811 2 0 1).toInstrSpec (sub_r32_r32_effect_step 0x12a811 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a80d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a811) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a813) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l12a80a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a80a :=
  Rest.liftedBlock (rest_l12a80a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a80a x hx)

theorem rest_l12a813 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a813 bytes_l12a813) (entryMap (live .l12a813))
      7 0x12a813 bytes_l12a813 b_l12a813 := by
  have f0 : InstrSpec 0x12a813 [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x12a813) (addR64Imm8Effect 0x12a813 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12a813 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x12a813 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a817 [0x5B] (PopPre 0x12a817) (popR64Effect 0x12a817 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12a817 1 3).toInstrSpec (pop_r64_effect_step 0x12a817 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x12a818 [0x41, 0x5C] (PopPre 0x12a818) (popR64Effect 0x12a818 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12a818 2 12).toInstrSpec (pop_r64_rex_effect_step 0x12a818 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x12a81a [0x41, 0x5E] (PopPre 0x12a81a) (popR64Effect 0x12a81a 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12a81a 2 14).toInstrSpec (pop_r64_rex_effect_step 0x12a81a 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x12a81c [0x41, 0x5F] (PopPre 0x12a81c) (popR64Effect 0x12a81c 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12a81c 2 15).toInstrSpec (pop_r64_rex_effect_step 0x12a81c 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x12a81e [0x5D] (PopPre 0x12a81e) (popR64Effect 0x12a81e 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12a81e 1 5).toInstrSpec (pop_r64_effect_step 0x12a81e 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x12a81f [0xC3] (RetPre 0x12a81f) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12a81f).toInstrSpec (ret_effect_step 0x12a81f) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a817) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a818) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a81a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a81c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (14, 61), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a81e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (14, 61), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a81f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (14, 61), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) f6 (by decide) rfl rfl rfl (by decide)

theorem block_l12a813 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a813 :=
  Rest.liftedBlock (rest_l12a813 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a813 x hx)

theorem rest_l12a820 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a820 bytes_l12a820) (entryMap (live .l12a820))
      16 0x12a820 bytes_l12a820 b_l12a820 := by
  have f0 : InstrSpec 0x12a820 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x12a820) (movR64R64Effect 0x12a820 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12a820 0 7).toInstrSpec (mov_r64_r64_effect_step 0x12a820 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a823 [0x41, 0x89, 0xC0] (fun s => s.RIP = 0x12a823) (movR32R32Effect 0x12a823 3 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x12a823 3 8 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x12a823 0x41 0xc0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a826 [0x41, 0xF7, 0xD8] (fun s => s.RIP = 0x12a826) (negR32Effect 0x12a826 3 8)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (negR32Effect_footprint 0x12a826 3 8).toInstrSpec (neg_r32_rex_effect_step 0x12a826 0x41 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12a829 [0x41, 0x83, 0xE0, 0x07] (fun s => s.RIP = 0x12a829) (andR32Imm8Effect 0x12a829 4 8 0x7)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x12a829 4 8 0x7).toInstrSpec (and_r32_imm8_rex_effect_step 0x12a829 0x41 0xe0 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a82d [0x4C, 0x39, 0xC2] (fun s => s.RIP = 0x12a82d) (cmpR64R64Effect 0x12a82d 2 8)
      [.gpr 2, .gpr 8] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12a82d 2 8).toInstrSpec (cmp_r64_r64_effect_step 0x12a82d 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12a830 [0x4C, 0x0F, 0x42, 0xC2] (fun s => s.RIP = 0x12a830) (atFlags (condHolds 2) (cmovR64R64Effect 0x12a830 4 8 2))
      [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .rip] :=
    (cmovR64R64Effect_footprint 0x12a830 4 8 2 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x12a830 2 0x4c (by decide) 0xc2 (by decide) c)) pre_rip
  have f6 : InstrSpec 0x12a834 [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x12a834) (movR64R64Effect 0x12a834 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a834 1 8).toInstrSpec (mov_r64_r64_effect_step 0x12a834 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12a837 [0xF3, 0xA4] (RepPre 0x12a837 (RepMovsbPre 0x12a837)) (repMovsbEffect 0x12a837)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsbEffect_footprint 0x12a837).toInstrSpecOfRuns (rep_movsb_runs hstride 0x12a837) (RepMovsOk.of_stateOf RepMovsbPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f8 : InstrSpec 0x12a839 [0x4C, 0x29, 0xC2] (fun s => s.RIP = 0x12a839) (subR64R64Effect 0x12a839 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x12a839 2 8).toInstrSpec (sub_r64_r64_effect_step 0x12a839 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x12a83c [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x12a83c) (movR64R64Effect 0x12a83c 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a83c 1 2).toInstrSpec (mov_r64_r64_effect_step 0x12a83c 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x12a83f [0x48, 0xC1, 0xE9, 0x03] (fun s => s.RIP = 0x12a83f) (shrR64Effect 0x12a83f 4 1 3)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x12a83f 4 1 3).toInstrSpec (shr_r64_imm8_effect_step 0x12a83f 0x48 0xe9 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12a843 [0xF3, 0x48, 0xA5] (RepPre 0x12a843 (RepMovsqPre 0x12a843)) (repMovsqEffect 0x12a843)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x12a843).toInstrSpecOfRuns (rep_movsq_runs hstride 0x12a843 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f12 : InstrSpec 0x12a846 [0x83, 0xE2, 0x07] (fun s => s.RIP = 0x12a846) (andR32Imm8Effect 0x12a846 3 2 0x7)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x12a846 3 2 0x7).toInstrSpec (and_r32_imm8_effect_step 0x12a846 0xe2 0x7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x12a849 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x12a849) (movR64R64Effect 0x12a849 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a849 1 2).toInstrSpec (mov_r64_r64_effect_step 0x12a849 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x12a84c [0xF3, 0xA4] (RepPre 0x12a84c (RepMovsbPre 0x12a84c)) (repMovsbEffect 0x12a84c)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsbEffect_footprint 0x12a84c).toInstrSpecOfRuns (rep_movsb_runs hstride 0x12a84c) (RepMovsOk.of_stateOf RepMovsbPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f15 : InstrSpec 0x12a84e [0xC3] (RetPre 0x12a84e) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12a84e).toInstrSpec (ret_effect_step 0x12a84e) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a823) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a826) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a829) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a82d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a830) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a834) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a837) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a839) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (2, 70), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a83c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 72), (2, 70), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a83f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 74), (2, 70), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a843) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(0, 53), (2, 70), (3, 3), (4, 4), (5, 5), (6, 76), (7, 77), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a846) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 53), (2, 79), (3, 3), (4, 4), (5, 5), (6, 76), (7, 77), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a849) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 53), (1, 81), (2, 79), (3, 3), (4, 4), (5, 5), (6, 76), (7, 77), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a84c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 84) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 85) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 86) (ρ' := [(0, 53), (1, 85), (2, 79), (3, 3), (4, 4), (5, 5), (6, 83), (7, 84), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a84e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f15 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 88) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 89) (ρ' := [(0, 53), (1, 85), (2, 79), (3, 3), (4, 88), (5, 5), (6, 83), (7, 84), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f15 (by decide) rfl rfl rfl (by decide)

theorem block_l12a820 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a820 :=
  Rest.liftedBlock (rest_l12a820 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a820 x hx)

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

theorem_by block_l1286fc_eval :
    program.runBlock (dialect code) ⟨.l1286fc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128705_eval :
    program.runBlock (dialect code) ⟨.l128705, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12870b_eval :
    program.runBlock (dialect code) ⟨.l12870b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128711_eval :
    program.runBlock (dialect code) ⟨.l128711, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128720_eval :
    program.runBlock (dialect code) ⟨.l128720, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a40_eval :
    program.runBlock (dialect code) ⟨.l128a40, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a4c_eval :
    program.runBlock (dialect code) ⟨.l128a4c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a52_eval :
    program.runBlock (dialect code) ⟨.l128a52, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a63_eval :
    program.runBlock (dialect code) ⟨.l128a63, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a69_eval :
    program.runBlock (dialect code) ⟨.l128a69, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a6f_eval :
    program.runBlock (dialect code) ⟨.l128a6f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a8b_eval :
    program.runBlock (dialect code) ⟨.l128a8b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a96_eval :
    program.runBlock (dialect code) ⟨.l128a96, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128ab2_eval :
    program.runBlock (dialect code) ⟨.l128ab2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128ab5_eval :
    program.runBlock (dialect code) ⟨.l128ab5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128ab9_eval :
    program.runBlock (dialect code) ⟨.l128ab9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128abe_eval :
    program.runBlock (dialect code) ⟨.l128abe, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128ad0_eval :
    program.runBlock (dialect code) ⟨.l128ad0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128af3_eval :
    program.runBlock (dialect code) ⟨.l128af3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129560_eval :
    program.runBlock (dialect code) ⟨.l129560, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129594_eval :
    program.runBlock (dialect code) ⟨.l129594, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1295a0_eval :
    program.runBlock (dialect code) ⟨.l1295a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1295f2_eval :
    program.runBlock (dialect code) ⟨.l1295f2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12962f_eval :
    program.runBlock (dialect code) ⟨.l12962f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129630_eval :
    program.runBlock (dialect code) ⟨.l129630, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12965d_eval :
    program.runBlock (dialect code) ⟨.l12965d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1296a9_eval :
    program.runBlock (dialect code) ⟨.l1296a9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1296eb_eval :
    program.runBlock (dialect code) ⟨.l1296eb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12974b_eval :
    program.runBlock (dialect code) ⟨.l12974b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129750_eval :
    program.runBlock (dialect code) ⟨.l129750, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129762_eval :
    program.runBlock (dialect code) ⟨.l129762, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129770_eval :
    program.runBlock (dialect code) ⟨.l129770, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12979c_eval :
    program.runBlock (dialect code) ⟨.l12979c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129b60_eval :
    program.runBlock (dialect code) ⟨.l129b60, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129b6d_eval :
    program.runBlock (dialect code) ⟨.l129b6d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129ba8_eval :
    program.runBlock (dialect code) ⟨.l129ba8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129bad_eval :
    program.runBlock (dialect code) ⟨.l129bad, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129bb2_eval :
    program.runBlock (dialect code) ⟨.l129bb2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129bed_eval :
    program.runBlock (dialect code) ⟨.l129bed, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c28_eval :
    program.runBlock (dialect code) ⟨.l129c28, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c30_eval :
    program.runBlock (dialect code) ⟨.l129c30, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c4c_eval :
    program.runBlock (dialect code) ⟨.l129c4c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c56_eval :
    program.runBlock (dialect code) ⟨.l129c56, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c5e_eval :
    program.runBlock (dialect code) ⟨.l129c5e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c63_eval :
    program.runBlock (dialect code) ⟨.l129c63, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c7b_eval :
    program.runBlock (dialect code) ⟨.l129c7b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c7d_eval :
    program.runBlock (dialect code) ⟨.l129c7d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c90_eval :
    program.runBlock (dialect code) ⟨.l129c90, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129cd0_eval :
    program.runBlock (dialect code) ⟨.l129cd0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129ce7_eval :
    program.runBlock (dialect code) ⟨.l129ce7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129d13_eval :
    program.runBlock (dialect code) ⟨.l129d13, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129d23_eval :
    program.runBlock (dialect code) ⟨.l129d23, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129d39_eval :
    program.runBlock (dialect code) ⟨.l129d39, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129d5f_eval :
    program.runBlock (dialect code) ⟨.l129d5f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a050_eval :
    program.runBlock (dialect code) ⟨.l12a050, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a070_eval :
    program.runBlock (dialect code) ⟨.l12a070, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a100_eval :
    program.runBlock (dialect code) ⟨.l12a100, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a430_eval :
    program.runBlock (dialect code) ⟨.l12a430, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a454_eval :
    program.runBlock (dialect code) ⟨.l12a454, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a470_eval :
    program.runBlock (dialect code) ⟨.l12a470, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a4c1_eval :
    program.runBlock (dialect code) ⟨.l12a4c1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a4c7_eval :
    program.runBlock (dialect code) ⟨.l12a4c7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a4f2_eval :
    program.runBlock (dialect code) ⟨.l12a4f2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a4f7_eval :
    program.runBlock (dialect code) ⟨.l12a4f7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a4fc_eval :
    program.runBlock (dialect code) ⟨.l12a4fc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a508_eval :
    program.runBlock (dialect code) ⟨.l12a508, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a52e_eval :
    program.runBlock (dialect code) ⟨.l12a52e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a700_eval :
    program.runBlock (dialect code) ⟨.l12a700, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a750_eval :
    program.runBlock (dialect code) ⟨.l12a750, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a771_eval :
    program.runBlock (dialect code) ⟨.l12a771, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a780_eval :
    program.runBlock (dialect code) ⟨.l12a780, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a7a3_eval :
    program.runBlock (dialect code) ⟨.l12a7a3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a7ac_eval :
    program.runBlock (dialect code) ⟨.l12a7ac, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a7b2_eval :
    program.runBlock (dialect code) ⟨.l12a7b2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a7be_eval :
    program.runBlock (dialect code) ⟨.l12a7be, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a7c0_eval :
    program.runBlock (dialect code) ⟨.l12a7c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a7c5_eval :
    program.runBlock (dialect code) ⟨.l12a7c5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a7ca_eval :
    program.runBlock (dialect code) ⟨.l12a7ca, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a7d0_eval :
    program.runBlock (dialect code) ⟨.l12a7d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a7d4_eval :
    program.runBlock (dialect code) ⟨.l12a7d4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a7e1_eval :
    program.runBlock (dialect code) ⟨.l12a7e1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a7e6_eval :
    program.runBlock (dialect code) ⟨.l12a7e6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a7f0_eval :
    program.runBlock (dialect code) ⟨.l12a7f0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a7f5_eval :
    program.runBlock (dialect code) ⟨.l12a7f5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a806_eval :
    program.runBlock (dialect code) ⟨.l12a806, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a80a_eval :
    program.runBlock (dialect code) ⟨.l12a80a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a813_eval :
    program.runBlock (dialect code) ⟨.l12a813, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a820_eval :
    program.runBlock (dialect code) ⟨.l12a820, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
