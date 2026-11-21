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

theorem rest_l107730 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107730 bytes_l107730) (entryMap (live .l107730))
      11 0x107730 bytes_l107730 b_l107730 := by
  have f0 : InstrSpec 0x107730 [0x55] (PushPre 0x107730 1) (pushR64Effect 0x107730 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107730 1 5).toInstrSpec (push_r64_effect_step 0x107730 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x107731 [0x41, 0x57] (PushPre 0x107731 2) (pushR64Effect 0x107731 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107731 2 15).toInstrSpec (push_r64_rex_effect_step 0x107731 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x107733 [0x41, 0x56] (PushPre 0x107733 2) (pushR64Effect 0x107733 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107733 2 14).toInstrSpec (push_r64_rex_effect_step 0x107733 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x107735 [0x41, 0x55] (PushPre 0x107735 2) (pushR64Effect 0x107735 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107735 2 13).toInstrSpec (push_r64_rex_effect_step 0x107735 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x107737 [0x41, 0x54] (PushPre 0x107737 2) (pushR64Effect 0x107737 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107737 2 12).toInstrSpec (push_r64_rex_effect_step 0x107737 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x107739 [0x53] (PushPre 0x107739 1) (pushR64Effect 0x107739 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107739 1 3).toInstrSpec (push_r64_effect_step 0x107739 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10773a [0x48, 0x83, 0xEC, 0x68] (fun s => s.RIP = 0x10773a) (subR64Imm8Effect 0x10773a 4 0x68)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10773a 4 0x68).toInstrSpec (sub_r64_imm8_effect_step 0x10773a 0x48 0xec 0x68 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10773e [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x10773e) (movR64R64Effect 0x10773e 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10773e 3 7).toInstrSpec (mov_r64_r64_effect_step 0x10773e 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x107741 [0x41, 0xBE, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107741) (movR32Imm32Effect 0x107741 6 14 0x1)
      [] [] [.reg 14, .rip] :=
    (movR32Imm32Effect_footprint 0x107741 6 14 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x107741 0x41 0xbe (by decide) (by decide) 0x1) pre_rip
  have f9 : InstrSpec 0x107747 [0x48, 0x83, 0xFA, 0x20] (fun s => s.RIP = 0x107747) (cmpR64Imm8Effect 0x107747 2 0x20)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x107747 2 0x20).toInstrSpec (cmp_r64_imm8_effect_step 0x107747 0x48 0xfa 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107731) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107733) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107735) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107737) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107739) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10773a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10773e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107741) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107747) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10774b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 73) (jcc_rel32_effect_step 0x10774b 5 0x146) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l107730 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107730 :=
  Rest.liftedBlock (rest_l107730 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107730 x hx)

theorem rest_l107751 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107751 bytes_l107751) (entryMap (live .l107751))
      19 0x107751 bytes_l107751 b_l107751 := by
  have f0 : InstrSpec 0x107751 [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x107751 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x107751 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107751 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107751 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x107751 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107755 [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x107755 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x107755 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107755 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107755 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x107755 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10775a [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x10775a (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10775a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10775a 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10775a 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10775a 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10775e [0x48, 0x89, 0x44, 0x24, 0x58] (StorePre 0x10775e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10775e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10775e 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10775e 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x10775e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x107763 [0x48, 0x8B, 0x06] (LoadPre 0x107763 (fun s => AddrMode.addr (.base 6 .none) s (0x107763 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x107763 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107763 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x107763 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x107766 [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x107766 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x107766 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107766 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x107766 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x107766 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10776a [0x48, 0x89, 0x4C, 0x24, 0x50] (StorePre 0x10776a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10776a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10776a 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10776a 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x10776a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10776f [0x48, 0x89, 0x44, 0x24, 0x48] (StorePre 0x10776f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10776f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10776f 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10776f 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x10776f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x107774 [0xC7, 0x44, 0x24, 0x04, 0x00, 0x01, 0x00, 0x00] (StorePre 0x107774 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x107774 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x107774 8 (.sib 4 none 0 (.d8 0x4)) 0x100)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x107774 8 (.sib 4 none 0 (.d8 0x4)) 0x100).toInstrSpec (mov_m32_imm32_effect_step 0x107774 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide) 0x100) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10777c [0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10777c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10777c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10777c (.sib 4 none 0 (.d8 0x40)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10777c (.sib 4 none 0 (.d8 0x40)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10777c 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x107785 [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107785 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107785 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107785 (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107785 (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107785 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x10778e [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10778e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10778e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10778e (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10778e (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10778e 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x107797 [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107797 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107797 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107797 (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107797 (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107797 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1077a0 [0x48, 0x8D, 0x7C, 0x24, 0x48] (fun s => s.RIP = 0x1077a0) (leaR64Effect 0x1077a0 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1077a0 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x1077a0 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1077a5 [0x48, 0x8D, 0x54, 0x24, 0x28] (fun s => s.RIP = 0x1077a5) (leaR64Effect 0x1077a5 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1077a5 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (lea_r64_effect_step 0x1077a5 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1077aa [0xBE, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1077aa) (movR32Imm32Effect 0x1077aa 5 6 0x20)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1077aa 5 6 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x1077aa 0xbe (by decide) 0x20) pre_rip
  have f16 : InstrSpec 0x1077af [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1077af) (movR32Imm32Effect 0x1077af 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1077af 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x1077af 0xb9 (by decide) 0x4) pre_rip
  have f17 : InstrSpec 0x1077b4 [0x41, 0xB8, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1077b4) (movR32Imm32Effect 0x1077b4 6 8 0x100)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x1077b4 6 8 0x100).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1077b4 0x41 0xb8 (by decide) (by decide) 0x100) pre_rip
  have f18 : InstrSpec 0x1077ba [0xE8, 0xB1, 0x05, 0x02, 0x00] (PushPre 0x1077ba 5) (callEffect (fun _ => 0x127d70) 0x1077bf)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1077ba 0x127d70 0x1077bf).toInstrSpec (call_rel32_effect_step 0x1077ba 0x205b1 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107755) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10775a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10775e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107763) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107766) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10776a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10776f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107774) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10777c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107785) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10778e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107797) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077a0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077a5) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 59), (1, 61), (2, 72), (3, 3), (4, 4), (5, 5), (6, 6), (7, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077aa) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 59), (1, 61), (2, 72), (3, 3), (4, 4), (5, 5), (6, 74), (7, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077af) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 59), (1, 76), (2, 72), (3, 3), (4, 4), (5, 5), (6, 74), (7, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077b4) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f17 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 59), (1, 76), (2, 72), (3, 3), (4, 4), (5, 5), (6, 74), (7, 70), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077ba) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 59), (1, 76), (2, 72), (3, 3), (4, 80), (5, 5), (6, 74), (7, 70), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d70) f18 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 82) (by decide) (by decide) rfl rfl

theorem block_l107751 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107751 :=
  Rest.liftedBlock (rest_l107751 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107751 x hx)

theorem rest_l1077bf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1077bf bytes_l1077bf) (entryMap (live .l1077bf))
      2 0x1077bf bytes_l1077bf b_l1077bf := by
  have f0 : InstrSpec 0x1077bf [0x3C, 0xFF] (fun s => s.RIP = 0x1077bf) (cmpAlImm8Effect 0x1077bf 0xff)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x1077bf 0xff).toInstrSpec (cmp_al_imm8_effect_step 0x1077bf 0xff) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1077c1 5 0xe5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1077bf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1077bf :=
  Rest.liftedBlock (rest_l1077bf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1077bf x hx)

theorem rest_l1077c7_2 [Bindings] (code : CodeMap) :
    Rest (n := 129) code lifted (codeRange 0x1077c7 bytes_l1077c7) [(1, 121), (2, 127), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x107868 bytes_l1077c7_2 b_l1077c7_2 := by
  have f40 : InstrSpec 0x107868 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x107868) (shrR64Effect 0x107868 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x107868 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x107868 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x10786c [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x10786c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10786c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10786c 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10786c 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10786c 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x107871 [0x0F, 0xB6, 0x44, 0x24, 0x08] (LoadPre 0x107871 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107871 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x107871 5 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x107871 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x107871 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f43 : InstrSpec 0x107876 [0x24, 0x01] (fun s => s.RIP = 0x107876) (andAlImm8Effect 0x107876 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x107876 0x1).toInstrSpec (and_al_imm8_effect_step 0x107876 0x1) pre_rip
  have f44 : InstrSpec 0x107878 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x107878) (movzxR32R8Effect 0x107878 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x107878 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x107878 0xf8 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x10787b [0xE8, 0xD0, 0x04, 0x02, 0x00] (PushPre 0x10787b 5) (callEffect (fun _ => 0x127d50) 0x107880)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10787b 0x127d50 0x107880).toInstrSpec (call_rel32_effect_step 0x10787b 0x204d0 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f40 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(1, 121), (2, 129), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10786c) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.exec (n := 131) (ρ' := [(1, 121), (2, 129), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107871) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f42 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 132), (1, 121), (2, 129), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107876) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f43 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 134), (1, 121), (2, 129), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107878) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f44 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 134), (1, 121), (2, 129), (3, 3), (4, 4), (5, 59), (6, 87), (7, 136), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10787b) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f45 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 134), (1, 121), (2, 129), (3, 3), (4, 138), (5, 59), (6, 87), (7, 136), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f45 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 140) (by decide) (by decide) rfl rfl

theorem rest_l1077c7_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x1077c7 bytes_l1077c7) [(1, 75), (2, 89), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]
      26 0x10781f bytes_l1077c7_1 b_l1077c7_1 := by
  have f20 : InstrSpec 0x10781f [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x10781f) (notR64Effect 0x10781f 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x10781f 2).toInstrSpec (not_r64_effect_step 0x10781f 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x107822 [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x107822) (orR64R64Effect 0x107822 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x107822 2 6).toInstrSpec (or_r64_r64_effect_step 0x107822 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x107825 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x107825) (shrR64Effect 0x107825 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x107825 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x107825 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x107829 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x107829 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107829 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107829 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107829 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x107829 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x10782e [0x48, 0x2B, 0x4C, 0x24, 0x08] (LoadPre 0x10782e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10782e + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10782e 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10782e 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x10782e 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x107833 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x107833) (sarR64Effect 0x107833 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x107833 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x107833 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x107837 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x107837) (movR64R64Effect 0x107837 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x107837 2 13).toInstrSpec (mov_r64_r64_effect_step 0x107837 0x4c 0xea (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x10783a [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x10783a) (notR64Effect 0x10783a 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x10783a 2).toInstrSpec (not_r64_effect_step 0x10783a 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10783d [0x4C, 0x01, 0xE9] (fun s => s.RIP = 0x10783d) (addR64R64Effect 0x10783d 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10783d 1 13).toInstrSpec (add_r64_r64_effect_step 0x10783d 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x107840 [0x48, 0x83, 0xC1, 0x02] (fun s => s.RIP = 0x107840) (addR64Imm8Effect 0x107840 1 0x2)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x107840 1 0x2).toInstrSpec (add_r64_imm8_effect_step 0x107840 0x48 0xc1 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x107844 [0x48, 0x09, 0xD1] (fun s => s.RIP = 0x107844) (orR64R64Effect 0x107844 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x107844 1 2).toInstrSpec (or_r64_r64_effect_step 0x107844 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x107847 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x107847) (shrR64Effect 0x107847 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x107847 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x107847 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10784b [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x10784b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10784b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10784b 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10784b 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10784b 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x107850 [0x48, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x107850 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107850 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107850 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x107850 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x107850 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f34 : InstrSpec 0x107855 [0x48, 0xFF, 0xC9] (fun s => s.RIP = 0x107855) (decR64Effect 0x107855 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (decR64Effect_footprint 0x107855 1).toInstrSpec (dec_r64_effect_step 0x107855 0x48 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x107858 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x107858) (shrR64Effect 0x107858 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x107858 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x107858 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x10785c [0x48, 0x01, 0xE9] (fun s => s.RIP = 0x10785c) (addR64R64Effect 0x10785c 1 5)
      [.gpr 1, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10785c 1 5).toInstrSpec (add_r64_r64_effect_step 0x10785c 0x48 0xe9 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x10785f [0x48, 0x89, 0xEA] (fun s => s.RIP = 0x10785f) (movR64R64Effect 0x10785f 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10785f 2 5).toInstrSpec (mov_r64_r64_effect_step 0x10785f 0x48 0xea (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x107862 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x107862) (notR64Effect 0x107862 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x107862 2).toInstrSpec (not_r64_effect_step 0x107862 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x107865 [0x48, 0x09, 0xCA] (fun s => s.RIP = 0x107865) (orR64R64Effect 0x107865 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x107865 2 1).toInstrSpec (or_r64_r64_effect_step 0x107865 0x48 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(1, 75), (2, 91), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107822) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(1, 75), (2, 93), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107825) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(1, 75), (2, 95), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107829) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(1, 75), (2, 95), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10782e) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(1, 98), (2, 95), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107833) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f25 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(1, 100), (2, 95), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107837) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f26 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(1, 100), (2, 102), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10783a) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f27 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(1, 100), (2, 104), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10783d) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f28 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(1, 106), (2, 104), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107840) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f29 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(1, 108), (2, 104), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107844) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f30 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(1, 110), (2, 104), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107847) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f31 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(1, 112), (2, 104), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10784b) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.exec (n := 114) (ρ' := [(1, 112), (2, 104), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107850) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f33 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(1, 115), (2, 104), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107855) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f34 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(1, 117), (2, 104), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107858) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f35 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(1, 119), (2, 104), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10785c) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(1, 121), (2, 104), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10785f) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(1, 121), (2, 123), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107862) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f38 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(1, 121), (2, 125), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107865) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f39 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(1, 121), (2, 127), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107868) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1077c7_2 code

theorem rest_l1077c7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1077c7 bytes_l1077c7) (entryMap (live .l1077c7))
      46 0x1077c7 bytes_l1077c7 b_l1077c7 := by
  have f0 : InstrSpec 0x1077c7 [0x4C, 0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x1077c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1077c7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1077c7 15 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x1077c7 15 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1077c7 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1077cc [0x4C, 0x8B, 0x64, 0x24, 0x30] (LoadPre 0x1077cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1077cc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1077cc 12 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x1077cc 12 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1077cc 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1077d1 [0x4C, 0x8B, 0x6C, 0x24, 0x38] (LoadPre 0x1077d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1077d1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1077d1 13 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x1077d1 13 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1077d1 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1077d6 [0x48, 0x8B, 0x6C, 0x24, 0x40] (LoadPre 0x1077d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1077d6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1077d6 5 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x1077d6 5 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1077d6 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1077db [0x48, 0xB8, 0xBF, 0xBE, 0xC9, 0x2F, 0x73, 0xA1, 0x2D, 0x40] (fun s => s.RIP = 0x1077db) (movR64Imm64Effect 0x1077db 0 0x402da1732fc9bebf)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x1077db 0 0x402da1732fc9bebf).toInstrSpec (mov_r64_imm64_effect_step 0x1077db 0x48 0xb8 (by decide) (by decide) 0x402da1732fc9bebf) pre_rip
  have f5 : InstrSpec 0x1077e5 [0x4C, 0x01, 0xF8] (fun s => s.RIP = 0x1077e5) (addR64R64Effect 0x1077e5 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1077e5 0 15).toInstrSpec (add_r64_r64_effect_step 0x1077e5 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1077e8 [0x4C, 0x89, 0xF9] (fun s => s.RIP = 0x1077e8) (movR64R64Effect 0x1077e8 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1077e8 1 15).toInstrSpec (mov_r64_r64_effect_step 0x1077e8 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1077eb [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x1077eb) (notR64Effect 0x1077eb 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x1077eb 1).toInstrSpec (not_r64_effect_step 0x1077eb 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1077ee [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x1077ee) (orR64R64Effect 0x1077ee 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1077ee 1 0).toInstrSpec (or_r64_r64_effect_step 0x1077ee 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1077f1 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x1077f1) (shrR64Effect 0x1077f1 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x1077f1 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x1077f1 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1077f5 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x1077f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1077f5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1077f5 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1077f5 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1077f5 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1077fa [0x48, 0x8D, 0x44, 0x24, 0x08] (fun s => s.RIP = 0x1077fa) (leaR64Effect 0x1077fa 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1077fa 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x1077fa 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1077ff [0x31, 0xC9] (fun s => s.RIP = 0x1077ff) (xorR32R32Effect 0x1077ff 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1077ff 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x1077ff 0xc9 (by decide)) pre_rip
  have f13 : InstrSpec 0x107801 [0x31, 0xD2] (fun s => s.RIP = 0x107801) (xorR32R32Effect 0x107801 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x107801 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x107801 0xd2 (by decide)) pre_rip
  have f14 : InstrSpec 0x107803 [0x48, 0x2B, 0x54, 0x24, 0x08] (LoadPre 0x107803 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107803 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x107803 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x107803 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x107803 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x107808 [0x48, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x107808) (sarR64Effect 0x107808 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (sarR64Effect_footprint 0x107808 4 2 63).toInstrSpec (sar_r64_imm8_effect_step 0x107808 0x48 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10780c [0x48, 0xBE, 0xC5, 0x5F, 0xB7, 0x50, 0x19, 0x23, 0x51, 0x45] (fun s => s.RIP = 0x10780c) (movR64Imm64Effect 0x10780c 6 0x4551231950b75fc5)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x10780c 6 0x4551231950b75fc5).toInstrSpec (mov_r64_imm64_effect_step 0x10780c 0x48 0xbe (by decide) (by decide) 0x4551231950b75fc5) pre_rip
  have f17 : InstrSpec 0x107816 [0x4C, 0x01, 0xE6] (fun s => s.RIP = 0x107816) (addR64R64Effect 0x107816 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x107816 6 12).toInstrSpec (add_r64_r64_effect_step 0x107816 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x107819 [0x48, 0x01, 0xD6] (fun s => s.RIP = 0x107819) (addR64R64Effect 0x107819 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x107819 6 2).toInstrSpec (add_r64_r64_effect_step 0x107819 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x10781c [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x10781c) (movR64R64Effect 0x10781c 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10781c 2 12).toInstrSpec (mov_r64_r64_effect_step 0x10781c 0x4c 0xe2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077cc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077d1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077d6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077db) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 2), (3, 3), (4, 4), (5, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077e5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (2, 2), (3, 3), (4, 4), (5, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077e8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 63), (1, 65), (2, 2), (3, 3), (4, 4), (5, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077eb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 63), (1, 67), (2, 2), (3, 3), (4, 4), (5, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077ee) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 63), (1, 69), (2, 2), (3, 3), (4, 4), (5, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077f1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 63), (1, 71), (2, 2), (3, 3), (4, 4), (5, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077f5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 63), (1, 71), (2, 2), (3, 3), (4, 4), (5, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077fa) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(1, 71), (2, 2), (3, 3), (4, 4), (5, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1077ff) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 75), (2, 2), (3, 3), (4, 4), (5, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107801) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 75), (2, 77), (3, 3), (4, 4), (5, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107803) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 75), (2, 79), (3, 3), (4, 4), (5, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107808) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(1, 75), (2, 81), (3, 3), (4, 4), (5, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10780c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(1, 75), (2, 81), (3, 3), (4, 4), (5, 59), (6, 83), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107816) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(1, 75), (2, 81), (3, 3), (4, 4), (5, 59), (6, 85), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107819) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(1, 75), (2, 81), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10781c) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(1, 75), (2, 89), (3, 3), (4, 4), (5, 59), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10781f) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1077c7_1 code

theorem block_l1077c7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1077c7 :=
  Rest.liftedBlock (rest_l1077c7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1077c7 x hx)

theorem rest_l107880 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107880 bytes_l107880) (entryMap (live .l107880))
      2 0x107880 bytes_l107880 b_l107880 := by
  have f0 : InstrSpec 0x107880 [0x3C, 0x01] (fun s => s.RIP = 0x107880) (cmpAlImm8Effect 0x107880 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x107880 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x107880 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107882) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x107882 5 0x13) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l107880 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107880 :=
  Rest.liftedBlock (rest_l107880 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107880 x hx)

theorem rest_l107884 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107884 bytes_l107884) (entryMap (live .l107884))
      5 0x107884 bytes_l107884 b_l107884 := by
  have f0 : InstrSpec 0x107884 [0x4C, 0x89, 0x7B, 0x08] (StorePre 0x107884 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x107884 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107884 15 (.base 3 (.d8 0x8)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x107884 15 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x107884 0x4c (by decide) 7 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x107888 [0x4C, 0x89, 0x63, 0x10] (StorePre 0x107888 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x107888 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107888 12 (.base 3 (.d8 0x10)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x107888 12 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x107888 0x4c (by decide) 4 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10788c [0x4C, 0x89, 0x6B, 0x18] (StorePre 0x10788c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x10788c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10788c 13 (.base 3 (.d8 0x18)))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10788c 13 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10788c 0x4c (by decide) 5 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x107890 [0x48, 0x89, 0x6B, 0x20] (StorePre 0x107890 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x107890 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107890 5 (.base 3 (.d8 0x20)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x107890 5 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x107890 0x48 (by decide) 5 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x107894 [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x107894) (xorR32R32Effect 0x107894 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x107894 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x107894 0x45 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107888) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10788c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107890) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107894) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107897) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l107884 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107884 :=
  Rest.liftedBlock (rest_l107884 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107884 x hx)

theorem rest_l107897 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107897 bytes_l107897) (entryMap (live .l107897))
      10 0x107897 bytes_l107897 b_l107897 := by
  have f0 : InstrSpec 0x107897 [0x4C, 0x89, 0x33] (StorePre 0x107897 3 (fun s => AddrMode.addr (.base 3 .none) s (0x107897 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x107897 14 (.base 3 .none))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x107897 14 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x107897 0x4c (by decide) 6 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10789a [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10789a) (movR64R64Effect 0x10789a 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10789a 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10789a 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10789d [0x48, 0x83, 0xC4, 0x68] (fun s => s.RIP = 0x10789d) (addR64Imm8Effect 0x10789d 4 0x68)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10789d 4 0x68).toInstrSpec (add_r64_imm8_effect_step 0x10789d 0x48 0xc4 0x68 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1078a1 [0x5B] (PopPre 0x1078a1) (popR64Effect 0x1078a1 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1078a1 1 3).toInstrSpec (pop_r64_effect_step 0x1078a1 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1078a2 [0x41, 0x5C] (PopPre 0x1078a2) (popR64Effect 0x1078a2 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1078a2 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1078a2 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1078a4 [0x41, 0x5D] (PopPre 0x1078a4) (popR64Effect 0x1078a4 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1078a4 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1078a4 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1078a6 [0x41, 0x5E] (PopPre 0x1078a6) (popR64Effect 0x1078a6 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1078a6 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1078a6 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1078a8 [0x41, 0x5F] (PopPre 0x1078a8) (popR64Effect 0x1078a8 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1078a8 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1078a8 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x1078aa [0x5D] (PopPre 0x1078aa) (popR64Effect 0x1078aa 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1078aa 1 5).toInstrSpec (pop_r64_effect_step 0x1078aa 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x1078ab [0xC3] (RetPre 0x1078ab) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1078ab).toInstrSpec (ret_effect_step 0x1078ab) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10789a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10789d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078a1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078a2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078a4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078a6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078a8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f7 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078aa) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 74), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078ab) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f9 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 78) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 77), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) f9 (by decide) rfl rfl rfl (by decide)

theorem block_l107897 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107897 :=
  Rest.liftedBlock (rest_l107897 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107897 x hx)

theorem rest_l1078ac [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1078ac bytes_l1078ac) (entryMap (live .l1078ac))
      9 0x1078ac bytes_l1078ac b_l1078ac := by
  have f0 : InstrSpec 0x1078ac [0x48, 0xC7, 0x44, 0x24, 0x08, 0x98, 0x24, 0x20, 0x00] (StorePre 0x1078ac 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1078ac + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1078ac (.sib 4 none 0 (.d8 0x8)) 0x202498)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1078ac (.sib 4 none 0 (.d8 0x8)) 0x202498).toInstrSpec (mov_m64_imm32_effect_step 0x1078ac 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x202498) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1078b5 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x90, 0xA1, 0x12, 0x00] (StorePre 0x1078b5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1078b5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1078b5 (.sib 4 none 0 (.d8 0x10)) 0x12a190)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1078b5 (.sib 4 none 0 (.d8 0x10)) 0x12a190).toInstrSpec (mov_m64_imm32_effect_step 0x1078b5 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x12a190) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1078be [0x48, 0x8D, 0x44, 0x24, 0x04] (fun s => s.RIP = 0x1078be) (leaR64Effect 0x1078be 0 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1078be 0 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (lea_r64_effect_step 0x1078be 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1078c3 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x1078c3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1078c3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1078c3 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1078c3 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1078c3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1078c8 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x90, 0xA1, 0x12, 0x00] (StorePre 0x1078c8 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1078c8 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1078c8 (.sib 4 none 0 (.d8 0x20)) 0x12a190)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1078c8 (.sib 4 none 0 (.d8 0x20)) 0x12a190).toInstrSpec (mov_m64_imm32_effect_step 0x1078c8 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x12a190) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1078d1 [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x1078d1) (leaR64Effect 0x1078d1 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1078d1 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x1078d1 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1078d6 [0x48, 0xC7, 0xC7, 0x8F, 0x02, 0x20, 0x00] (fun s => s.RIP = 0x1078d6) (movR64Imm32Effect 0x1078d6 7 0x20028f)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x1078d6 7 0x20028f).toInstrSpec (mov_r64_imm32_effect_step 0x1078d6 0x48 0xc7 (by decide) (by decide) (by decide) 0x20028f) pre_rip
  have f7 : InstrSpec 0x1078dd [0x48, 0xC7, 0xC2, 0x18, 0x25, 0x20, 0x00] (fun s => s.RIP = 0x1078dd) (movR64Imm32Effect 0x1078dd 2 0x202518)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x1078dd 2 0x202518).toInstrSpec (mov_r64_imm32_effect_step 0x1078dd 0x48 0xc2 (by decide) (by decide) (by decide) 0x202518) pre_rip
  have f8 : InstrSpec 0x1078e4 [0xE8, 0x87, 0x1E, 0x02, 0x00] (PushPre 0x1078e4 5) (callEffect (fun _ => 0x129770) 0x1078e9)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1078e4 0x129770 0x1078e9).toInstrSpec (call_rel32_effect_step 0x1078e4 0x21e87 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x1078b5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5)]) (p' := 0x1078be) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (4, 4), (5, 5)]) (p' := 0x1078c3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (4, 4), (5, 5)]) (p' := 0x1078c8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (4, 4), (5, 5)]) (p' := 0x1078d1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (4, 4), (5, 5), (6, 59)]) (p' := 0x1078d6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (4, 4), (5, 5), (6, 59), (7, 61)]) (p' := 0x1078dd) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (2, 63), (4, 4), (5, 5), (6, 59), (7, 61)]) (p' := 0x1078e4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (2, 63), (4, 65), (5, 5), (6, 59), (7, 61)]) (p' := 0x129770) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l1078ac [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1078ac :=
  Rest.liftedBlock (rest_l1078ac code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1078ac x hx)

theorem rest_l1078e9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1078e9 bytes_l1078e9) (entryMap (live .l1078e9))
      12 0x1078e9 bytes_l1078e9 b_l1078e9 := by
  have f0 : InstrSpec 0x1078e9 [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1078e9) (fun _ => nopEffect 0x1078e9 7)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1078e9 7).toInstrSpec (nop_m_effect_step 0x1078e9 [] (by decide) (by decide) (.base 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1078f0 [0x48, 0x83, 0xEC, 0x18] (fun s => s.RIP = 0x1078f0) (subR64Imm8Effect 0x1078f0 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1078f0 4 0x18).toInstrSpec (sub_r64_imm8_effect_step 0x1078f0 0x48 0xec 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1078f4 [0x48, 0x8B, 0x07] (LoadPre 0x1078f4 (fun s => AddrMode.addr (.base 7 .none) s (0x1078f4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1078f4 0 (.base 7 .none))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1078f4 0 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1078f4 0x48 (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1078f7 [0x48, 0x8B, 0x3E] (LoadPre 0x1078f7 (fun s => AddrMode.addr (.base 6 .none) s (0x1078f7 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1078f7 7 (.base 6 .none))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1078f7 7 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1078f7 0x48 (by decide) 7 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1078fa [0x48, 0x8B, 0x76, 0x08] (LoadPre 0x1078fa (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1078fa + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1078fa 6 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1078fa 6 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1078fa 0x48 (by decide) 6 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1078fe [0x48, 0x89, 0x04, 0x24] (StorePre 0x1078fe 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1078fe + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1078fe 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1078fe 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1078fe 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x107902 [0x48, 0x89, 0xE0] (fun s => s.RIP = 0x107902) (movR64R64Effect 0x107902 0 4)
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x107902 0 4).toInstrSpec (mov_r64_r64_effect_step 0x107902 0x48 0xe0 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x107905 [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x107905 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107905 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107905 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107905 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x107905 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10790a [0x48, 0xC7, 0x44, 0x24, 0x10, 0xC0, 0x79, 0x10, 0x00] (StorePre 0x10790a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10790a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10790a (.sib 4 none 0 (.d8 0x10)) 0x1079c0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10790a (.sib 4 none 0 (.d8 0x10)) 0x1079c0).toInstrSpec (mov_m64_imm32_effect_step 0x10790a 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x1079c0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x107913 [0x48, 0x8D, 0x4C, 0x24, 0x08] (fun s => s.RIP = 0x107913) (leaR64Effect 0x107913 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x107913 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x107913 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x107918 [0x48, 0xC7, 0xC2, 0x13, 0x04, 0x20, 0x00] (fun s => s.RIP = 0x107918) (movR64Imm32Effect 0x107918 2 0x200413)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x107918 2 0x200413).toInstrSpec (mov_r64_imm32_effect_step 0x107918 0x48 0xc2 (by decide) (by decide) (by decide) 0x200413) pre_rip
  have f11 : InstrSpec 0x10791f [0xE8, 0x7C, 0x1A, 0x02, 0x00] (PushPre 0x10791f 5) (callEffect (fun _ => 0x1293a0) 0x107924)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10791f 0x1293a0 0x107924).toInstrSpec (call_rel32_effect_step 0x10791f 0x21a7c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078f0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078f4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078f7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (3, 3), (4, 54), (5, 5), (6, 6), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078fa) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 56), (3, 3), (4, 54), (5, 5), (6, 60), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1078fe) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 56), (3, 3), (4, 54), (5, 5), (6, 60), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107902) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (3, 3), (4, 54), (5, 5), (6, 60), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107905) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (3, 3), (4, 54), (5, 5), (6, 60), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10790a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 63), (3, 3), (4, 54), (5, 5), (6, 60), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107913) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 63), (1, 67), (3, 3), (4, 54), (5, 5), (6, 60), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107918) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 63), (1, 67), (2, 69), (3, 3), (4, 54), (5, 5), (6, 60), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10791f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 63), (1, 67), (2, 69), (3, 3), (4, 71), (5, 5), (6, 60), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293a0) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l1078e9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1078e9 :=
  Rest.liftedBlock (rest_l1078e9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1078e9 x hx)

theorem rest_l107924 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107924 bytes_l107924) (entryMap (live .l107924))
      2 0x107924 bytes_l107924 b_l107924 := by
  have f0 : InstrSpec 0x107924 [0x48, 0x83, 0xC4, 0x18] (fun s => s.RIP = 0x107924) (addR64Imm8Effect 0x107924 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x107924 4 0x18).toInstrSpec (add_r64_imm8_effect_step 0x107924 0x48 0xc4 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x107928 [0xC3] (RetPre 0x107928) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x107928).toInstrSpec (ret_effect_step 0x107928) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107928) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f1 (by decide) rfl rfl rfl (by decide)

theorem block_l107924 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107924 :=
  Rest.liftedBlock (rest_l107924 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107924 x hx)

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

theorem_by block_l107730_eval :
    program.runBlock (dialect code) ⟨.l107730, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107751_eval :
    program.runBlock (dialect code) ⟨.l107751, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1077bf_eval :
    program.runBlock (dialect code) ⟨.l1077bf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1077c7_eval :
    program.runBlock (dialect code) ⟨.l1077c7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107880_eval :
    program.runBlock (dialect code) ⟨.l107880, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107884_eval :
    program.runBlock (dialect code) ⟨.l107884, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107897_eval :
    program.runBlock (dialect code) ⟨.l107897, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1078ac_eval :
    program.runBlock (dialect code) ⟨.l1078ac, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1078e9_eval :
    program.runBlock (dialect code) ⟨.l1078e9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107924_eval :
    program.runBlock (dialect code) ⟨.l107924, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
