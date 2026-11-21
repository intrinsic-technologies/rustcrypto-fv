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
      13 0x12962f bytes_l12962f b_l12962f := by
  have f0 : InstrSpec 0x12962f [0x90] (fun s => s.RIP = 0x12962f) (fun _ => nopEffect 0x12962f 1)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12962f 1).toInstrSpec (nop_effect_step 0x12962f) pre_rip
  have f1 : InstrSpec 0x129630 [0x55] (PushPre 0x129630 1) (pushR64Effect 0x129630 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129630 1 5).toInstrSpec (push_r64_effect_step 0x129630 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x129631 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129631) (movR64R64Effect 0x129631 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129631 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129631 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129634 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x129634) (subR64Imm8Effect 0x129634 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x129634 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x129634 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129638 [0x48, 0x89, 0x7D, 0xD8] (StorePre 0x129638 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x129638 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129638 7 (.base 5 (.d8 0xd8)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129638 7 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x129638 0x48 (by decide) 7 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12963c [0x48, 0x89, 0x75, 0xE0] (StorePre 0x12963c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x12963c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12963c 6 (.base 5 (.d8 0xe0)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12963c 6 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x12963c 0x48 (by decide) 6 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x129640 [0x48, 0x8D, 0x45, 0xD8] (fun s => s.RIP = 0x129640) (leaR64Effect 0x129640 0 (.base 5 (.d8 0xd8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129640 0 (.base 5 (.d8 0xd8))).toInstrSpec (lea_r64_effect_step 0x129640 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x129644 [0x48, 0x89, 0x45, 0xE8] (StorePre 0x129644 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x129644 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129644 0 (.base 5 (.d8 0xe8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129644 0 (.base 5 (.d8 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x129644 0x48 (by decide) 0 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x129648 [0x48, 0x89, 0x4D, 0xF0] (StorePre 0x129648 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x129648 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129648 1 (.base 5 (.d8 0xf0)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129648 1 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x129648 0x48 (by decide) 1 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12964c [0xC6, 0x45, 0xF8, 0x00] (StorePre 0x12964c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x12964c + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x12964c (.base 5 (.d8 0xf8)) 0x0)
      [.gpr 5] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x12964c (.base 5 (.d8 0xf8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x12964c (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x129650 [0x88, 0x55, 0xF9] (StorePre 0x129650 3 (fun s => AddrMode.addr (.base 5 (.d8 0xf9)) s (0x129650 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x129650 3 2 (.base 5 (.d8 0xf9)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM8R8Effect_footprint 0x129650 3 2 (.base 5 (.d8 0xf9))).toInstrSpec (mov_m8_r8_effect_step 0x129650 2 (by decide) (.base 5 (.d8 0xf9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x129653 [0x48, 0x8D, 0x7D, 0xE8] (fun s => s.RIP = 0x129653) (leaR64Effect 0x129653 7 (.base 5 (.d8 0xe8)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x129653 7 (.base 5 (.d8 0xe8))).toInstrSpec (lea_r64_effect_step 0x129653 0x48 (by decide) 7 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x129657 [0xFF, 0x15, 0xC3, 0xA7, 0x0D, 0x00] (GoesTo (CallMemPre 0x129657 (.rip 0xda7c3)) (callEffect (callMemPtr 0x129657 (.rip 0xda7c3)) (0x129657 + BitVec.ofNat 64 (callMemLen (.rip 0xda7c3)))) 0x100a20) (callEffect (callMemPtr 0x129657 (.rip 0xda7c3)) (0x129657 + BitVec.ofNat 64 (callMemLen (.rip 0xda7c3))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x129657 (.rip 0xda7c3)).toInstrSpec (call_m64_effect_step 0x129657 (.rip 0xda7c3) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x100a20
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x129630) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (4, 54), (5, 5), (6, 6), (7, 7)]) (p' := 0x129631) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 1), (2, 2), (4, 54), (5, 56), (6, 6), (7, 7)]) (p' := 0x129634) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 1), (2, 2), (4, 58), (5, 56), (6, 6), (7, 7)]) (p' := 0x129638) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (4, 58), (5, 56), (6, 6), (7, 7)]) (p' := 0x12963c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(1, 1), (2, 2), (4, 58), (5, 56), (6, 6), (7, 7)]) (p' := 0x129640) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 1), (2, 2), (4, 58), (5, 56), (6, 6), (7, 7)]) (p' := 0x129644) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 1), (2, 2), (4, 58), (5, 56), (6, 6), (7, 7)]) (p' := 0x129648) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 1), (2, 2), (4, 58), (5, 56), (6, 6), (7, 7)]) (p' := 0x12964c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 1), (2, 2), (4, 58), (5, 56), (6, 6), (7, 7)]) (p' := 0x129650) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 1), (2, 2), (4, 58), (5, 56), (6, 6), (7, 7)]) (p' := 0x129653) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 62), (1, 1), (2, 2), (4, 58), (5, 56), (6, 6)]) (p' := 0x129657) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 62), (1, 1), (2, 2), (5, 56), (6, 6)]) (p' := 0x100a20) f12 (fun _ h => h.2) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 70) (by decide) (by decide) rfl rfl

theorem block_l12962f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12962f :=
  Rest.liftedBlock (rest_l12962f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12962f x hx)

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
      5 0x12974b bytes_l12974b b_l12974b := by
  have f0 : InstrSpec 0x12974b [0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x12974b) (fun _ => nopEffect 0x12974b 5)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12974b 5).toInstrSpec (nop_m_effect_step 0x12974b [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129750 [0x55] (PushPre 0x129750 1) (pushR64Effect 0x129750 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129750 1 5).toInstrSpec (push_r64_effect_step 0x129750 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x129751 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129751) (movR64R64Effect 0x129751 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129751 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129751 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129754 [0x48, 0x8D, 0x34, 0x75, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129754) (leaR64Effect 0x129754 6 (.abs (some 6) 1 0x1))
      [.gpr 6] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x129754 6 (.abs (some 6) 1 0x1)).toInstrSpec (lea_r64_effect_step 0x129754 0x48 (by decide) 6 (.abs (some 6) 1 0x1) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12975c [0xFF, 0x15, 0x7E, 0xA6, 0x0D, 0x00] (GoesTo (CallMemPre 0x12975c (.rip 0xda67e)) (callEffect (callMemPtr 0x12975c (.rip 0xda67e)) (0x12975c + BitVec.ofNat 64 (callMemLen (.rip 0xda67e)))) 0x129770) (callEffect (callMemPtr 0x12975c (.rip 0xda67e)) (0x12975c + BitVec.ofNat 64 (callMemLen (.rip 0xda67e))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x12975c (.rip 0xda67e)).toInstrSpec (call_m64_effect_step 0x12975c (.rip 0xda67e) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x129750) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (4, 54), (5, 5), (6, 6), (7, 7)]) (p' := 0x129751) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (4, 54), (5, 56), (6, 6), (7, 7)]) (p' := 0x129754) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 2), (4, 54), (5, 56), (6, 58), (7, 7)]) (p' := 0x12975c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 2), (4, 60), (5, 56), (6, 58), (7, 7)]) (p' := 0x129770) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l12974b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12974b :=
  Rest.liftedBlock (rest_l12974b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12974b x hx)

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

theorem_by block_l129762_eval :
    program.runBlock (dialect code) ⟨.l129762, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Sec1.LIR
