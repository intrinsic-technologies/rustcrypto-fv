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

theorem rest_l100a40 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100a40 bytes_l100a40) (entryMap (live .l100a40))
      12 0x100a40 bytes_l100a40 b_l100a40 := by
  have f0 : InstrSpec 0x100a40 [0x55] (PushPre 0x100a40 1) (pushR64Effect 0x100a40 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100a40 1 5).toInstrSpec (push_r64_effect_step 0x100a40 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x100a41 [0x41, 0x57] (PushPre 0x100a41 2) (pushR64Effect 0x100a41 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100a41 2 15).toInstrSpec (push_r64_rex_effect_step 0x100a41 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x100a43 [0x41, 0x56] (PushPre 0x100a43 2) (pushR64Effect 0x100a43 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100a43 2 14).toInstrSpec (push_r64_rex_effect_step 0x100a43 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x100a45 [0x41, 0x55] (PushPre 0x100a45 2) (pushR64Effect 0x100a45 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100a45 2 13).toInstrSpec (push_r64_rex_effect_step 0x100a45 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x100a47 [0x41, 0x54] (PushPre 0x100a47 2) (pushR64Effect 0x100a47 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100a47 2 12).toInstrSpec (push_r64_rex_effect_step 0x100a47 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x100a49 [0x53] (PushPre 0x100a49 1) (pushR64Effect 0x100a49 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100a49 1 3).toInstrSpec (push_r64_effect_step 0x100a49 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x100a4a [0x48, 0x81, 0xEC, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100a4a) (subR64Imm32Effect 0x100a4a 4 0xb8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x100a4a 4 0xb8).toInstrSpec (sub_r64_imm32_effect_step 0x100a4a 0x48 0xec 0xb8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100a51 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x100a51) (movR64R64Effect 0x100a51 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x100a51 13 2).toInstrSpec (mov_r64_r64_effect_step 0x100a51 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100a54 [0x48, 0x89, 0x74, 0x24, 0x28] (StorePre 0x100a54 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100a54 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100a54 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100a54 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x100a54 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x100a59 [0x48, 0x8D, 0x4F, 0x08] (fun s => s.RIP = 0x100a59) (leaR64Effect 0x100a59 1 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x100a59 1 (.base 7 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x100a59 0x48 (by decide) 1 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x100a5d [0x48, 0x81, 0xFA, 0xFF, 0xFF, 0xFF, 0x1F] (fun s => s.RIP = 0x100a5d) (cmpR64Imm32Effect 0x100a5d 2 0x1fffffff)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm32Effect_footprint 0x100a5d 2 0x1fffffff).toInstrSpec (cmp_r64_imm32_effect_step 0x100a5d 0x48 0xfa 0x1fffffff (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a41) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a43) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a45) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a47) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a49) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a4a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a51) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a54) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a59) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 70), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a5d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 70), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 14), (15, 15), (16, 72), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a64) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 75) (jcc_rel32_effect_step 0x100a64 7 0x400) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100a40 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100a40 :=
  Rest.liftedBlock (rest_l100a40 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100a40 x hx)

theorem rest_l100a6a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100a6a bytes_l100a6a) (entryMap (live .l100a6a))
      12 0x100a6a bytes_l100a6a b_l100a6a := by
  have f0 : InstrSpec 0x100a6a [0x42, 0x8D, 0x04, 0xED, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100a6a) (leaR32Effect 0x100a6a 8 0 (.abs (some 13) 3 0x0))
      [.gpr 13] [] [.reg 0, .rip] :=
    (leaR32Effect_footprint 0x100a6a 8 0 (.abs (some 13) 3 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x100a6a 0x42 (by decide) 0 (.abs (some 13) 3 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100a72 [0x89, 0x44, 0x24, 0x38] (StorePre 0x100a72 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x100a72 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100a72 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100a72 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m32_r32_low_effect_step 0x100a72 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x100a76 [0x48, 0x89, 0xBC, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x100a76 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x100a76 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100a76 7 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100a76 7 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x100a76 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x100a7e [0x48, 0x8D, 0x47, 0x28] (fun s => s.RIP = 0x100a7e) (leaR64Effect 0x100a7e 0 (.base 7 (.d8 0x28)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x100a7e 0 (.base 7 (.d8 0x28))).toInstrSpec (lea_r64_effect_step 0x100a7e 0x48 (by decide) 0 (.base 7 (.d8 0x28)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100a82 [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x100a82 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x100a82 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100a82 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100a82 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x100a82 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x100a8a [0x48, 0x89, 0xCF] (fun s => s.RIP = 0x100a8a) (movR64R64Effect 0x100a8a 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x100a8a 7 1).toInstrSpec (mov_r64_r64_effect_step 0x100a8a 0x48 0xcf (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100a8d [0x48, 0x89, 0x4C, 0x24, 0x40] (StorePre 0x100a8d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100a8d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100a8d 1 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100a8d 1 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x100a8d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x100a92 [0x4C, 0x89, 0x6C, 0x24, 0x30] (StorePre 0x100a92 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100a92 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100a92 13 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100a92 13 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x100a92 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x100a97 [0x4D, 0x85, 0xED] (fun s => s.RIP = 0x100a97) (testR64R64Effect 0x100a97 13 13)
      [.gpr 13, .gpr 13] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x100a97 13 13).toInstrSpec (test_r64_r64_effect_step 0x100a97 0x4d 0xed (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x100a9a [0x4C, 0x8B, 0xA4, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x100a9a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x100a9a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100a9a 12 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x100a9a 12 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x100a9a 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x100aa2 [0x48, 0x8D, 0x1D, 0x77, 0x9D, 0x02, 0x00] (fun s => s.RIP = 0x100aa2) (leaR64Effect 0x100aa2 3 (.rip 0x29d77))
      [] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x100aa2 3 (.rip 0x29d77)).toInstrSpec (lea_r64_effect_step 0x100aa2 0x48 (by decide) 3 (.rip 0x29d77) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a72) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a76) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a7e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a82) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 57), (1, 1), (2, 2), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a8a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 57), (1, 1), (2, 2), (4, 4), (5, 5), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a8d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 1), (2, 2), (4, 4), (5, 5), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a92) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 57), (1, 1), (2, 2), (4, 4), (5, 5), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a97) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 57), (1, 1), (2, 2), (4, 4), (5, 5), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a9a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 57), (1, 1), (2, 2), (4, 4), (5, 5), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 66), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100aa2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 68), (4, 4), (5, 5), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 66), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100aa9) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 70) (jcc_rel8_effect_step 0x100aa9 4 0x44) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100a6a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100a6a :=
  Rest.liftedBlock (rest_l100a6a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100a6a x hx)

theorem rest_l100aab [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100aab bytes_l100aab) (entryMap (live .l100aab))
      1 0x100aab bytes_l100aab b_l100aab := by
  have f0 : InstrSpec 0x100aab [0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x100aab) (fun _ => nopEffect 0x100aab 5)
      [] [] [.rip] :=
    (nopEffect_footprint 0x100aab 5).toInstrSpec (nop_m_effect_step 0x100aab [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ab0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l100aab [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100aab :=
  Rest.liftedBlock (rest_l100aab code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100aab x hx)

theorem rest_l100ab0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100ab0 bytes_l100ab0) (entryMap (live .l100ab0))
      3 0x100ab0 bytes_l100ab0 b_l100ab0 := by
  have f0 : InstrSpec 0x100ab0 [0x4C, 0x8B, 0x74, 0x24, 0x28] (LoadPre 0x100ab0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100ab0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100ab0 14 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x100ab0 14 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x100ab0 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100ab5 [0x48, 0x8B, 0x6C, 0x24, 0x30] (LoadPre 0x100ab5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100ab5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100ab5 5 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x100ab5 5 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x100ab5 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100aba [0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x100aba) (fun _ => nopEffect 0x100aba 6)
      [] [] [.rip] :=
    (nopEffect_footprint 0x100aba 6).toInstrSpec (nop_m_effect_step 0x100aba [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ab5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100aba) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ac0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l100ab0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100ab0 :=
  Rest.liftedBlock (rest_l100ab0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100ab0 x hx)

theorem rest_l100ac0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100ac0 bytes_l100ac0) (entryMap (live .l100ac0))
      5 0x100ac0 bytes_l100ac0 b_l100ac0 := by
  have f0 : InstrSpec 0x100ac0 [0x48, 0x83, 0xFD, 0x20] (fun s => s.RIP = 0x100ac0) (cmpR64Imm8Effect 0x100ac0 5 0x20)
      [.gpr 5] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100ac0 5 0x20).toInstrSpec (cmp_r64_imm8_effect_step 0x100ac0 0x48 0xfd 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100ac4 [0x41, 0xBF, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100ac4) (movR32Imm32Effect 0x100ac4 6 15 0x20)
      [] [] [.reg 15, .rip] :=
    (movR32Imm32Effect_footprint 0x100ac4 6 15 0x20).toInstrSpec (mov_r32_imm32_rex_effect_step 0x100ac4 0x41 0xbf (by decide) (by decide) 0x20) pre_rip
  have f2 : InstrSpec 0x100aca [0x4C, 0x0F, 0x42, 0xFD] (fun s => s.RIP = 0x100aca) (atFlags (condHolds 2) (cmovR64R64Effect 0x100aca 4 15 5))
      [.gpr 15, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .rip] :=
    (cmovR64R64Effect_footprint 0x100aca 4 15 5 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x100aca 2 0x4c (by decide) 0xfd (by decide) c)) pre_rip
  have f3 : InstrSpec 0x100ace [0x4F, 0x8D, 0x2C, 0x3E] (fun s => s.RIP = 0x100ace) (leaR64Effect 0x100ace 13 (.sib 14 (some 15) 0 .none))
      [.gpr 14, .gpr 15] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x100ace 13 (.sib 14 (some 15) 0 .none)).toInstrSpec (lea_r64_effect_step 0x100ace 0x4f (by decide) 5 (.sib 14 (some 15) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100ad2 [0xE8, 0x99, 0x3E, 0x00, 0x00] (PushPre 0x100ad2 5) (callEffect (fun _ => 0x104970) 0x100ad7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100ad2 0x104970 0x100ad7).toInstrSpec (call_rel32_effect_step 0x100ad2 0x3e99 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ac4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 55), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100aca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 57), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ace) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 57), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ad2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 57), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104970) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l100ac0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100ac0 :=
  Rest.liftedBlock (rest_l100ac0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100ac0 x hx)

theorem rest_l100ad7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100ad7 bytes_l100ad7) (entryMap (live .l100ad7))
      4 0x100ad7 bytes_l100ad7 b_l100ad7 := by
  have f0 : InstrSpec 0x100ad7 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x100ad7) (movR64R64Effect 0x100ad7 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x100ad7 7 14).toInstrSpec (mov_r64_r64_effect_step 0x100ad7 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100ada [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x100ada) (movR64R64Effect 0x100ada 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100ada 6 12).toInstrSpec (mov_r64_r64_effect_step 0x100ada 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100add [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x100add) (movR64R64Effect 0x100add 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x100add 2 15).toInstrSpec (mov_r64_r64_effect_step 0x100add 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100ae0 [0xFF, 0xD3] (GoesTo (CallPre 0x100ae0 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x100ae2) 0x12a820) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x100ae2)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x100ae0 3 0x100ae2).toInstrSpec (call_r64_effect_step 0x100ae0 0xd3 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 3 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ada) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100add) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ae0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l100ad7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100ad7 :=
  Rest.liftedBlock (rest_l100ad7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100ad7 x hx)

theorem rest_l100ae2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100ae2 bytes_l100ae2) (entryMap (live .l100ae2))
      4 0x100ae2 bytes_l100ae2 b_l100ae2 := by
  have f0 : InstrSpec 0x100ae2 [0x48, 0x8B, 0x7C, 0x24, 0x40] (LoadPre 0x100ae2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100ae2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100ae2 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x100ae2 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x100ae2 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100ae7 [0x4D, 0x89, 0xEE] (fun s => s.RIP = 0x100ae7) (movR64R64Effect 0x100ae7 14 13)
      [.gpr 13] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x100ae7 14 13).toInstrSpec (mov_r64_r64_effect_step 0x100ae7 0x4d 0xee (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100aea [0x4C, 0x29, 0xFD] (fun s => s.RIP = 0x100aea) (subR64R64Effect 0x100aea 5 15)
      [.gpr 5, .gpr 15] [] [.reg 5, .flags, .rip] :=
    (subR64R64Effect_footprint 0x100aea 5 15).toInstrSpec (sub_r64_r64_effect_step 0x100aea 0x4c 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ae7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100aea) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100aed) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x100aed 5 0xd1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100ae2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100ae2 :=
  Rest.liftedBlock (rest_l100ae2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100ae2 x hx)

theorem rest_l100aef [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100aef bytes_l100aef) (entryMap (live .l100aef))
      3 0x100aef bytes_l100aef b_l100aef := by
  have f0 : InstrSpec 0x100aef [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100aef) (movR32Imm32Effect 0x100aef 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x100aef 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x100aef 0xbe (by decide) 0x8) pre_rip
  have f1 : InstrSpec 0x100af4 [0x31, 0xD2] (fun s => s.RIP = 0x100af4) (xorR32R32Effect 0x100af4 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100af4 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x100af4 0xd2 (by decide)) pre_rip
  have f2 : InstrSpec 0x100af6 [0xE8, 0x35, 0x34, 0x00, 0x00] (PushPre 0x100af6 5) (callEffect (fun _ => 0x103f30) 0x100afb)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100af6 0x103f30 0x100afb).toInstrSpec (call_rel32_effect_step 0x100af6 0x3435 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100af4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100af6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 57), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f30) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l100aef [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100aef :=
  Rest.liftedBlock (rest_l100aef code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100aef x hx)

theorem rest_l100afb_2 [Bindings] (code : CodeMap) :
    Rest (n := 129) code lifted (codeRange 0x100afb bytes_l100afb) [(0, 72), (1, 93), (2, 127), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 114), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]
      15 0x100b98 bytes_l100afb_2 b_l100afb_2 := by
  have f40 : InstrSpec 0x100b98 [0xF7, 0xDA] (fun s => s.RIP = 0x100b98) (negR32Effect 0x100b98 2 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR32Effect_footprint 0x100b98 2 2).toInstrSpec (neg_r32_effect_step 0x100b98 0xda (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x100b9a [0x21, 0xF2] (fun s => s.RIP = 0x100b9a) (andR32R32Effect 0x100b9a 2 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100b9a 2 2 6).toInstrSpec (and_r32_r32_effect_step 0x100b9a 0xf2 (by decide)) pre_rip
  have f42 : InstrSpec 0x100b9c [0x01, 0xC1] (fun s => s.RIP = 0x100b9c) (addR32R32Effect 0x100b9c 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100b9c 2 1 0).toInstrSpec (add_r32_r32_effect_step 0x100b9c 0xc1 (by decide)) pre_rip
  have f43 : InstrSpec 0x100b9e [0x44, 0x01, 0xC2] (fun s => s.RIP = 0x100b9e) (addR32R32Effect 0x100b9e 3 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100b9e 3 2 8).toInstrSpec (add_r32_r32_rex_effect_step 0x100b9e 0x44 0xc2 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x100ba1 [0x01, 0xCA] (fun s => s.RIP = 0x100ba1) (addR32R32Effect 0x100ba1 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100ba1 2 2 1).toInstrSpec (add_r32_r32_effect_step 0x100ba1 0xca (by decide)) pre_rip
  have f45 : InstrSpec 0x100ba3 [0xB8, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x100ba3) (movR32Imm32Effect 0x100ba3 5 0 0x100)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x100ba3 5 0 0x100).toInstrSpec (mov_r32_imm32_effect_step 0x100ba3 0xb8 (by decide) 0x100) pre_rip
  have f46 : InstrSpec 0x100ba8 [0x29, 0xD0] (fun s => s.RIP = 0x100ba8) (subR32R32Effect 0x100ba8 2 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (subR32R32Effect_footprint 0x100ba8 2 0 2).toInstrSpec (sub_r32_r32_effect_step 0x100ba8 0xd0 (by decide)) pre_rip
  have f47 : InstrSpec 0x100baa [0x44, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x100baa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x100baa + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100baa 8 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x100baa 8 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r32_m32_effect_step 0x100baa 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f48 : InstrSpec 0x100baf [0x45, 0x89, 0xC6] (fun s => s.RIP = 0x100baf) (movR32R32Effect 0x100baf 3 14 8)
      [.gpr 8] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x100baf 3 14 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x100baf 0x45 0xc6 (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x100bb2 [0x41, 0x29, 0xC6] (fun s => s.RIP = 0x100bb2) (subR32R32Effect 0x100bb2 3 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (subR32R32Effect_footprint 0x100bb2 3 14 0).toInstrSpec (sub_r32_r32_rex_effect_step 0x100bb2 0x41 0xc6 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x100bb5 [0xBA, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100bb5) (movR32Imm32Effect 0x100bb5 5 2 0x0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x100bb5 5 2 0x0).toInstrSpec (mov_r32_imm32_effect_step 0x100bb5 0xba (by decide) 0x0) pre_rip
  have f51 : InstrSpec 0x100bba [0x45, 0x0F, 0x42, 0xF1] (fun s => s.RIP = 0x100bba) (atFlags (condHolds 2) (cmovR32R32Effect 0x100bba 4 14 9))
      [.gpr 14, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .rip] :=
    (cmovR32R32Effect_footprint 0x100bba 4 14 9 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_rex_effect_step 0x100bba 2 0x45 (by decide) 0xf1 (by decide) c)) pre_rip
  have f52 : InstrSpec 0x100bbe [0x44, 0x89, 0xF1] (fun s => s.RIP = 0x100bbe) (movR32R32Effect 0x100bbe 3 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x100bbe 3 1 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x100bbe 0x44 0xf1 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x100bc1 [0xC1, 0xE9, 0x03] (fun s => s.RIP = 0x100bc1) (shrR32Effect 0x100bc1 3 1 3)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x100bc1 3 1 3).toInstrSpec (shr_r32_imm8_effect_step 0x100bc1 0xe9 0x3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f40 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 72), (1, 93), (2, 129), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 114), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b9a) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f41 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 72), (1, 93), (2, 131), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 114), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b9c) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f42 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 72), (1, 133), (2, 131), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 114), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b9e) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f43 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 72), (1, 133), (2, 135), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 114), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ba1) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f44 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 72), (1, 133), (2, 137), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 114), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ba3) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f45 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 139), (1, 133), (2, 137), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 114), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ba8) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f46 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 141), (1, 133), (2, 137), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 114), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100baa) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f47 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 141), (1, 133), (2, 137), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 143), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100baf) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f48 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 141), (1, 133), (2, 137), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 143), (9, 97), (10, 10), (11, 11), (12, 66), (14, 145), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bb2) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f49 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 148) f49 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 149) (ρ' := [(0, 141), (1, 133), (2, 137), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 143), (9, 97), (10, 10), (11, 11), (12, 66), (14, 147), (15, 55), (16, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bb5) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f50 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 141), (1, 133), (2, 150), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 143), (9, 97), (10, 10), (11, 11), (12, 66), (14, 147), (15, 55), (16, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bba) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f51 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 141), (1, 133), (2, 150), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 143), (9, 97), (10, 10), (11, 11), (12, 66), (14, 152), (15, 55), (16, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bbe) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f52 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 141), (1, 154), (2, 150), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 143), (9, 97), (10, 10), (11, 11), (12, 66), (14, 152), (15, 55), (16, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bc1) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f53 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 157) f53 .ZF (fun _ => rfl) (shrR32Effect_fresh 0x100bc1 3 1 3 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 158) (ρ' := [(0, 141), (1, 156), (2, 150), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 143), (9, 97), (10, 10), (11, 11), (12, 66), (14, 152), (15, 55), (19, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bc4) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 159) (jcc_rel8_effect_step 0x100bc4 4 0x2a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l100afb_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x100afb bytes_l100afb) [(0, 72), (1, 89), (2, 87), (3, 3), (4, 4), (5, 5), (6, 74), (7, 80), (10, 10), (11, 11), (12, 66), (15, 55), (19, 84), (22, 22), (39, 39), (50, 50), (51, 51)]
      35 0x100b4b bytes_l100afb_1 b_l100afb_1 := by
  have f20 : InstrSpec 0x100b4b [0xF7, 0xD9] (fun s => s.RIP = 0x100b4b) (negR32Effect 0x100b4b 2 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR32Effect_footprint 0x100b4b 2 1).toInstrSpec (neg_r32_effect_step 0x100b4b 0xd9 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x100b4d [0x21, 0xF9] (fun s => s.RIP = 0x100b4d) (andR32R32Effect 0x100b4d 2 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100b4d 2 1 7).toInstrSpec (and_r32_r32_effect_step 0x100b4d 0xf9 (by decide)) pre_rip
  have f22 : InstrSpec 0x100b4f [0x48, 0x85, 0xF6] (fun s => s.RIP = 0x100b4f) (testR64R64Effect 0x100b4f 6 6)
      [.gpr 6, .gpr 6] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x100b4f 6 6).toInstrSpec (test_r64_r64_effect_step 0x100b4f 0x48 0xf6 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x100b52 [0x41, 0xB9, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100b52) (movR32Imm32Effect 0x100b52 6 9 0x0)
      [] [] [.reg 9, .rip] :=
    (movR32Imm32Effect_footprint 0x100b52 6 9 0x0).toInstrSpec (mov_r32_imm32_rex_effect_step 0x100b52 0x41 0xb9 (by decide) (by decide) 0x0) pre_rip
  have f24 : InstrSpec 0x100b58 [0x41, 0x0F, 0x45, 0xD1] (fun s => s.RIP = 0x100b58) (atFlags (condHolds 5) (cmovR32R32Effect 0x100b58 4 2 9))
      [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR32R32Effect_footprint 0x100b58 4 2 9 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_rex_effect_step 0x100b58 5 0x41 (by decide) 0xd1 (by decide) c)) pre_rip
  have f25 : InstrSpec 0x100b5c [0x49, 0x8B, 0x77, 0x08] (LoadPre 0x100b5c (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x100b5c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100b5c 6 (.base 15 (.d8 0x8)))
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x100b5c 6 (.base 15 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x100b5c 0x49 (by decide) 6 (.base 15 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x100b60 [0xBF, 0x7F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100b60) (movR32Imm32Effect 0x100b60 5 7 0x7f)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x100b60 5 7 0x7f).toInstrSpec (mov_r32_imm32_effect_step 0x100b60 0xbf (by decide) 0x7f) pre_rip
  have f27 : InstrSpec 0x100b65 [0x48, 0x0F, 0xBD, 0xFE] (fun s => s.RIP = 0x100b65) (bsrR64R64Effect 0x100b65 4 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (bsrR64R64Effect_footprint 0x100b65 4 7 6).toInstrSpec (bsr_r64_r64_effect_step 0x100b65 0x48 (by decide) 0xfe (by decide)) pre_rip
  have f28 : InstrSpec 0x100b69 [0x83, 0xF7, 0x3F] (fun s => s.RIP = 0x100b69) (xorR32Imm8Effect 0x100b69 3 7 0x3f)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x100b69 3 7 0x3f).toInstrSpec (xor_r32_imm8_effect_step 0x100b69 0xf7 0x3f (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x100b6c [0x88, 0x54, 0x24, 0x08] (StorePre 0x100b6c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100b6c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x100b6c 4 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x100b6c 4 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_effect_step 0x100b6c 2 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x100b70 [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x08] (LoadPre 0x100b70 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100b70 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x100b70 6 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x100b70 6 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x100b70 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x100b76 [0x41, 0xF7, 0xD8] (fun s => s.RIP = 0x100b76) (negR32Effect 0x100b76 3 8)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (negR32Effect_footprint 0x100b76 3 8).toInstrSpec (neg_r32_rex_effect_step 0x100b76 0x41 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x100b79 [0x41, 0x21, 0xF8] (fun s => s.RIP = 0x100b79) (andR32R32Effect 0x100b79 3 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100b79 3 8 7).toInstrSpec (and_r32_r32_rex_effect_step 0x100b79 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x100b7c [0x48, 0x85, 0xF6] (fun s => s.RIP = 0x100b7c) (testR64R64Effect 0x100b7c 6 6)
      [.gpr 6, .gpr 6] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x100b7c 6 6).toInstrSpec (test_r64_r64_effect_step 0x100b7c 0x48 0xf6 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x100b7f [0x41, 0x0F, 0x45, 0xD1] (fun s => s.RIP = 0x100b7f) (atFlags (condHolds 5) (cmovR32R32Effect 0x100b7f 4 2 9))
      [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR32R32Effect_footprint 0x100b7f 4 2 9 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_rex_effect_step 0x100b7f 5 0x41 (by decide) 0xd1 (by decide) c)) pre_rip
  have f35 : InstrSpec 0x100b83 [0xBE, 0x7F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100b83) (movR32Imm32Effect 0x100b83 5 6 0x7f)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x100b83 5 6 0x7f).toInstrSpec (mov_r32_imm32_effect_step 0x100b83 0xbe (by decide) 0x7f) pre_rip
  have f36 : InstrSpec 0x100b88 [0x49, 0x0F, 0xBD, 0x37] (LoadPre 0x100b88 (fun s => AddrMode.addr (.base 15 .none) s (0x100b88 + BitVec.ofNat 64 4)) 8) (bsrR64M64Effect 0x100b88 4 6 (.base 15 .none))
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (bsrR64M64Effect_footprint 0x100b88 4 6 (.base 15 .none)).toInstrSpec (bsr_r64_m64_effect_step 0x100b88 0x49 (by decide) 6 (.base 15 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x100b8c [0x83, 0xF6, 0x3F] (fun s => s.RIP = 0x100b8c) (xorR32Imm8Effect 0x100b8c 3 6 0x3f)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x100b8c 3 6 0x3f).toInstrSpec (xor_r32_imm8_effect_step 0x100b8c 0xf6 0x3f (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x100b8f [0x88, 0x54, 0x24, 0x08] (StorePre 0x100b8f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100b8f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x100b8f 4 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x100b8f 4 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_effect_step 0x100b8f 2 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x100b93 [0x0F, 0xB6, 0x54, 0x24, 0x08] (LoadPre 0x100b93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100b93 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100b93 5 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x100b93 5 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x100b93 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 72), (1, 91), (2, 87), (3, 3), (4, 4), (5, 5), (6, 74), (7, 80), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b4d) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 72), (1, 93), (2, 87), (3, 3), (4, 4), (5, 5), (6, 74), (7, 80), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b4f) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 72), (1, 93), (2, 87), (3, 3), (4, 4), (5, 5), (6, 74), (7, 80), (10, 10), (11, 11), (12, 66), (15, 55), (19, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b52) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 72), (1, 93), (2, 87), (3, 3), (4, 4), (5, 5), (6, 74), (7, 80), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (19, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b58) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 72), (1, 93), (2, 99), (3, 3), (4, 4), (5, 5), (6, 74), (7, 80), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (19, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b5c) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f25 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 72), (1, 93), (2, 99), (3, 3), (4, 4), (5, 5), (6, 101), (7, 80), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (19, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b60) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 72), (1, 93), (2, 99), (3, 3), (4, 4), (5, 5), (6, 101), (7, 103), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (19, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b65) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 72), (1, 93), (2, 99), (3, 3), (4, 4), (5, 5), (6, 101), (7, 105), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b69) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f28 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 72), (1, 93), (2, 99), (3, 3), (4, 4), (5, 5), (6, 101), (7, 107), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b6c) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.exec (n := 109) (ρ' := [(0, 72), (1, 93), (2, 99), (3, 3), (4, 4), (5, 5), (6, 101), (7, 107), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b70) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f30 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 72), (1, 93), (2, 99), (3, 3), (4, 4), (5, 5), (6, 101), (7, 107), (8, 110), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b76) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f31 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 72), (1, 93), (2, 99), (3, 3), (4, 4), (5, 5), (6, 101), (7, 107), (8, 112), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b79) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f32 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 72), (1, 93), (2, 99), (3, 3), (4, 4), (5, 5), (6, 101), (7, 107), (8, 114), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b7c) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f33 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 72), (1, 93), (2, 99), (3, 3), (4, 4), (5, 5), (6, 101), (7, 107), (8, 114), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (19, 116), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b7f) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f34 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 72), (1, 93), (2, 118), (3, 3), (4, 4), (5, 5), (6, 101), (7, 107), (8, 114), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (19, 116), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b83) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f35 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 72), (1, 93), (2, 118), (3, 3), (4, 4), (5, 5), (6, 120), (7, 107), (8, 114), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (19, 116), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b88) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f36 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 72), (1, 93), (2, 118), (3, 3), (4, 4), (5, 5), (6, 122), (7, 107), (8, 114), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b8c) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f37 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 72), (1, 93), (2, 118), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 114), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b8f) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.exec (n := 126) (ρ' := [(0, 72), (1, 93), (2, 118), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 114), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b93) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f39 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 72), (1, 93), (2, 127), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 114), (9, 97), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b98) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100afb_2 code

theorem rest_l100afb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100afb bytes_l100afb) (entryMap (live .l100afb))
      55 0x100afb bytes_l100afb b_l100afb := by
  have f0 : InstrSpec 0x100afb [0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x100afb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x100afb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100afb 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100afb 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x100afb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100b03 [0x4C, 0x8B, 0x38] (LoadPre 0x100b03 (fun s => AddrMode.addr (.base 0 .none) s (0x100b03 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100b03 15 (.base 0 .none))
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x100b03 15 (.base 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x100b03 0x4c (by decide) 7 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100b06 [0x49, 0x8B, 0x4F, 0x18] (LoadPre 0x100b06 (fun s => AddrMode.addr (.base 15 (.d8 0x18)) s (0x100b06 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100b06 1 (.base 15 (.d8 0x18)))
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100b06 1 (.base 15 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x100b06 0x49 (by decide) 1 (.base 15 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x100b0a [0xBA, 0x7F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100b0a) (movR32Imm32Effect 0x100b0a 5 2 0x7f)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x100b0a 5 2 0x7f).toInstrSpec (mov_r32_imm32_effect_step 0x100b0a 0xba (by decide) 0x7f) pre_rip
  have f4 : InstrSpec 0x100b0f [0x48, 0x0F, 0xBD, 0xD1] (fun s => s.RIP = 0x100b0f) (bsrR64R64Effect 0x100b0f 4 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (bsrR64R64Effect_footprint 0x100b0f 4 2 1).toInstrSpec (bsr_r64_r64_effect_step 0x100b0f 0x48 (by decide) 0xd1 (by decide)) pre_rip
  have f5 : InstrSpec 0x100b13 [0x83, 0xF2, 0x3F] (fun s => s.RIP = 0x100b13) (xorR32Imm8Effect 0x100b13 3 2 0x3f)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x100b13 3 2 0x3f).toInstrSpec (xor_r32_imm8_effect_step 0x100b13 0xf2 0x3f (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100b16 [0xC6, 0x44, 0x24, 0x08, 0x01] (StorePre 0x100b16 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100b16 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x100b16 (.sib 4 none 0 (.d8 0x8)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x100b16 (.sib 4 none 0 (.d8 0x8)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x100b16 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x100b1b [0x4C, 0x8D, 0x64, 0x24, 0x08] (fun s => s.RIP = 0x100b1b) (leaR64Effect 0x100b1b 12 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x100b1b 12 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x100b1b 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100b20 [0x0F, 0xB6, 0x44, 0x24, 0x08] (LoadPre 0x100b20 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100b20 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100b20 5 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x100b20 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x100b20 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x100b25 [0xF7, 0xD8] (fun s => s.RIP = 0x100b25) (negR32Effect 0x100b25 2 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR32Effect_footprint 0x100b25 2 0).toInstrSpec (neg_r32_effect_step 0x100b25 0xd8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x100b27 [0x21, 0xD0] (fun s => s.RIP = 0x100b27) (andR32R32Effect 0x100b27 2 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100b27 2 0 2).toInstrSpec (and_r32_r32_effect_step 0x100b27 0xd0 (by decide)) pre_rip
  have f11 : InstrSpec 0x100b29 [0x49, 0x8B, 0x77, 0x10] (LoadPre 0x100b29 (fun s => AddrMode.addr (.base 15 (.d8 0x10)) s (0x100b29 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100b29 6 (.base 15 (.d8 0x10)))
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x100b29 6 (.base 15 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x100b29 0x49 (by decide) 6 (.base 15 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x100b2d [0xBF, 0x7F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100b2d) (movR32Imm32Effect 0x100b2d 5 7 0x7f)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x100b2d 5 7 0x7f).toInstrSpec (mov_r32_imm32_effect_step 0x100b2d 0xbf (by decide) 0x7f) pre_rip
  have f13 : InstrSpec 0x100b32 [0x48, 0x0F, 0xBD, 0xFE] (fun s => s.RIP = 0x100b32) (bsrR64R64Effect 0x100b32 4 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (bsrR64R64Effect_footprint 0x100b32 4 7 6).toInstrSpec (bsr_r64_r64_effect_step 0x100b32 0x48 (by decide) 0xfe (by decide)) pre_rip
  have f14 : InstrSpec 0x100b36 [0x83, 0xF7, 0x3F] (fun s => s.RIP = 0x100b36) (xorR32Imm8Effect 0x100b36 3 7 0x3f)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x100b36 3 7 0x3f).toInstrSpec (xor_r32_imm8_effect_step 0x100b36 0xf7 0x3f (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x100b39 [0x31, 0xD2] (fun s => s.RIP = 0x100b39) (xorR32R32Effect 0x100b39 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100b39 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x100b39 0xd2 (by decide)) pre_rip
  have f16 : InstrSpec 0x100b3b [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x100b3b) (testR64R64Effect 0x100b3b 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x100b3b 1 1).toInstrSpec (test_r64_r64_effect_step 0x100b3b 0x48 0xc9 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x100b3e [0x0F, 0x94, 0x44, 0x24, 0x08] (StorePre 0x100b3e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100b3e + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x100b3e 5 (.sib 4 none 0 (.d8 0x8))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x100b3e 5 (.sib 4 none 0 (.d8 0x8)) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x100b3e 4 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x100b43 [0x0F, 0x94, 0xC2] (fun s => s.RIP = 0x100b43) (atFlags (condHolds 4) (setccR8Effect 0x100b43 3 2))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (setccR8Effect_footprint 0x100b43 3 2 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x100b43 4 0xc2 (by decide) (by decide) c)) pre_rip
  have f19 : InstrSpec 0x100b46 [0x0F, 0xB6, 0x4C, 0x24, 0x08] (LoadPre 0x100b46 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100b46 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100b46 5 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x100b46 5 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x100b46 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b03) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b06) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b0a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b0f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 57), (2, 61), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b13) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 57), (2, 63), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b16) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 57), (2, 63), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b1b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 57), (2, 63), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b20) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 57), (2, 63), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b25) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (1, 57), (2, 63), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b27) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 57), (2, 63), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b29) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 72), (1, 57), (2, 63), (3, 3), (4, 4), (5, 5), (6, 74), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b2d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 72), (1, 57), (2, 63), (3, 3), (4, 4), (5, 5), (6, 74), (7, 76), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b32) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 72), (1, 57), (2, 63), (3, 3), (4, 4), (5, 5), (6, 74), (7, 78), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b36) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 72), (1, 57), (2, 63), (3, 3), (4, 4), (5, 5), (6, 74), (7, 80), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b39) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 72), (1, 57), (2, 82), (3, 3), (4, 4), (5, 5), (6, 74), (7, 80), (10, 10), (11, 11), (12, 66), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b3b) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 72), (1, 57), (2, 82), (3, 3), (4, 4), (5, 5), (6, 74), (7, 80), (10, 10), (11, 11), (12, 66), (15, 55), (19, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b3e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 72), (1, 57), (2, 82), (3, 3), (4, 4), (5, 5), (6, 74), (7, 80), (10, 10), (11, 11), (12, 66), (15, 55), (19, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b43) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 72), (1, 57), (2, 87), (3, 3), (4, 4), (5, 5), (6, 74), (7, 80), (10, 10), (11, 11), (12, 66), (15, 55), (19, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b46) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 72), (1, 89), (2, 87), (3, 3), (4, 4), (5, 5), (6, 74), (7, 80), (10, 10), (11, 11), (12, 66), (15, 55), (19, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b4b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100afb_1 code

theorem block_l100afb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100afb :=
  Rest.liftedBlock (rest_l100afb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100afb x hx)

theorem rest_l100bc6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100bc6 bytes_l100bc6) (entryMap (live .l100bc6))
      5 0x100bc6 bytes_l100bc6 b_l100bc6 := by
  have f0 : InstrSpec 0x100bc6 [0x89, 0xC9] (fun s => s.RIP = 0x100bc6) (movR32R32Effect 0x100bc6 2 1 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x100bc6 2 1 1).toInstrSpec (mov_r32_r32_effect_step 0x100bc6 0xc9 (by decide)) pre_rip
  have f1 : InstrSpec 0x100bc8 [0x4C, 0x8B, 0x6C, 0x24, 0x30] (LoadPre 0x100bc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100bc8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100bc8 13 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x100bc8 13 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x100bc8 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100bcd [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x100bcd) (movR64R64Effect 0x100bcd 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100bcd 6 13).toInstrSpec (mov_r64_r64_effect_step 0x100bcd 0x4c 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100bd0 [0x48, 0x29, 0xCE] (fun s => s.RIP = 0x100bd0) (subR64R64Effect 0x100bd0 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (subR64R64Effect_footprint 0x100bd0 6 1).toInstrSpec (sub_r64_r64_effect_step 0x100bd0 0x48 0xce (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bc8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bcd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bd0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (16, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bd3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel32_effect_step 0x100bd3 2 0x243) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100bc6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100bc6 :=
  Rest.liftedBlock (rest_l100bc6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100bc6 x hx)

theorem rest_l100bd9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100bd9 bytes_l100bd9) (entryMap (live .l100bd9))
      6 0x100bd9 bytes_l100bd9 b_l100bd9 := by
  have f0 : InstrSpec 0x100bd9 [0x41, 0x83, 0xE6, 0xF8] (fun s => s.RIP = 0x100bd9) (andR32Imm8Effect 0x100bd9 4 14 0xf8)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x100bd9 4 14 0xf8).toInstrSpec (and_r32_imm8_rex_effect_step 0x100bd9 0x41 0xe6 0xf8 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100bdd [0x45, 0x29, 0xF0] (fun s => s.RIP = 0x100bdd) (subR32R32Effect 0x100bdd 3 8 14)
      [.gpr 8, .gpr 14] [] [.reg 8, .flags, .rip] :=
    (subR32R32Effect_footprint 0x100bdd 3 8 14).toInstrSpec (sub_r32_r32_rex_effect_step 0x100bdd 0x45 0xf0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100be0 [0x45, 0x89, 0xC6] (fun s => s.RIP = 0x100be0) (movR32R32Effect 0x100be0 3 14 8)
      [.gpr 8] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x100be0 3 14 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x100be0 0x45 0xc6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100be3 [0x41, 0x29, 0xC6] (fun s => s.RIP = 0x100be3) (subR32R32Effect 0x100be3 3 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (subR32R32Effect_footprint 0x100be3 3 14 0).toInstrSpec (sub_r32_r32_rex_effect_step 0x100be3 0x41 0xc6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100be6 [0x44, 0x0F, 0x42, 0xF2] (fun s => s.RIP = 0x100be6) (atFlags (condHolds 2) (cmovR32R32Effect 0x100be6 4 14 2))
      [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .rip] :=
    (cmovR32R32Effect_footprint 0x100be6 4 14 2 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_rex_effect_step 0x100be6 2 0x44 (by decide) 0xf2 (by decide) c)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bdd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100be0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100be3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (16, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100be6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (16, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bea) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 64) (jmp_rel8_effect_step 0x100bea 0xc (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100bd9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100bd9 :=
  Rest.liftedBlock (rest_l100bd9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100bd9 x hx)

theorem rest_l100bf0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100bf0 bytes_l100bf0) (entryMap (live .l100bf0))
      2 0x100bf0 bytes_l100bf0 b_l100bf0 := by
  have f0 : InstrSpec 0x100bf0 [0x4C, 0x8B, 0x6C, 0x24, 0x30] (LoadPre 0x100bf0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100bf0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100bf0 13 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x100bf0 13 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x100bf0 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100bf5 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x100bf5) (movR64R64Effect 0x100bf5 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100bf5 6 13).toInstrSpec (mov_r64_r64_effect_step 0x100bf5 0x4c 0xee (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bf5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bf8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l100bf0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100bf0 :=
  Rest.liftedBlock (rest_l100bf0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100bf0 x hx)

theorem rest_l100bf8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100bf8 bytes_l100bf8) (entryMap (live .l100bf8))
      9 0x100bf8 bytes_l100bf8 b_l100bf8 := by
  have f0 : InstrSpec 0x100bf8 [0x44, 0x89, 0x44, 0x24, 0x3C] (StorePre 0x100bf8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x100bf8 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100bf8 8 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100bf8 8 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_m32_r32_effect_step 0x100bf8 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x100bfd [0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100bfd 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x100bfd + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100bfd (.sib 4 none 0 (.d32 0x80)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100bfd (.sib 4 none 0 (.d32 0x80)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100bfd 0x48 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x100c09 [0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100c09 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x100c09 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100c09 (.sib 4 none 0 (.d8 0x78)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100c09 (.sib 4 none 0 (.d8 0x78)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100c09 0x48 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x100c12 [0x48, 0xC7, 0x44, 0x24, 0x70, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100c12 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x100c12 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100c12 (.sib 4 none 0 (.d8 0x70)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100c12 (.sib 4 none 0 (.d8 0x70)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100c12 0x48 (by decide) (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x100c1b [0x48, 0xC7, 0x44, 0x24, 0x68, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100c1b 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x100c1b + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100c1b (.sib 4 none 0 (.d8 0x68)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100c1b (.sib 4 none 0 (.d8 0x68)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100c1b 0x48 (by decide) (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x100c24 [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100c24) (movR32Imm32Effect 0x100c24 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x100c24 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x100c24 0xb9 (by decide) 0x4) pre_rip
  have f6 : InstrSpec 0x100c29 [0x48, 0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x100c29 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100c29 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100c29 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x100c29 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x100c29 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x100c2e [0x48, 0x8D, 0x54, 0x24, 0x68] (fun s => s.RIP = 0x100c2e) (leaR64Effect 0x100c2e 2 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x100c2e 2 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (lea_r64_effect_step 0x100c2e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100c33 [0xE8, 0x38, 0x71, 0x02, 0x00] (PushPre 0x100c33 5) (callEffect (fun _ => 0x127d70) 0x100c38)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100c33 0x127d70 0x100c38).toInstrSpec (call_rel32_effect_step 0x100c33 0x27138 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bfd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c09) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c12) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c1b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c24) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c29) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c2e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 58), (2, 62), (3, 3), (4, 4), (5, 5), (6, 6), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c33) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 58), (2, 62), (3, 3), (4, 64), (5, 5), (6, 6), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d70) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l100bf8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100bf8 :=
  Rest.liftedBlock (rest_l100bf8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100bf8 x hx)

theorem rest_l100c38 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100c38 bytes_l100c38) (entryMap (live .l100c38))
      2 0x100c38 bytes_l100c38 b_l100c38 := by
  have f0 : InstrSpec 0x100c38 [0x3C, 0xFF] (fun s => s.RIP = 0x100c38) (cmpAlImm8Effect 0x100c38 0xff)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x100c38 0xff).toInstrSpec (cmp_al_imm8_effect_step 0x100c38 0xff) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c3a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x100c3a 5 0x1ed) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100c38 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100c38 :=
  Rest.liftedBlock (rest_l100c38 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100c38 x hx)

theorem rest_l100c40 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100c40 bytes_l100c40) (entryMap (live .l100c40))
      12 0x100c40 bytes_l100c40 b_l100c40 := by
  have f0 : InstrSpec 0x100c40 [0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x100c40 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x100c40 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100c40 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100c40 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x100c40 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100c48 [0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x100c48 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x100c48 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100c48 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100c48 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x100c48 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x100c50 [0x48, 0x8B, 0x44, 0x24, 0x78] (LoadPre 0x100c50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x100c50 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100c50 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100c50 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x100c50 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x100c55 [0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x100c55 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x100c55 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100c55 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100c55 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x100c55 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x100c5d [0x48, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x100c5d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x100c5d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100c5d 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100c5d 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x100c5d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x100c62 [0x48, 0x8B, 0x4C, 0x24, 0x70] (LoadPre 0x100c62 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x100c62 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100c62 1 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100c62 1 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x100c62 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x100c67 [0x48, 0x89, 0x8C, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x100c67 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x100c67 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100c67 1 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100c67 1 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x100c67 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x100c6f [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x100c6f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x100c6f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100c6f 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100c6f 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x100c6f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x100c77 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x100c77) (movR64R64Effect 0x100c77 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x100c77 7 12).toInstrSpec (mov_r64_r64_effect_step 0x100c77 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x100c7a [0x48, 0x8D, 0xB4, 0x24, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100c7a) (leaR64Effect 0x100c7a 6 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x100c7a 6 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (lea_r64_effect_step 0x100c7a 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x100c82 [0x44, 0x89, 0xF2] (fun s => s.RIP = 0x100c82) (movR32R32Effect 0x100c82 3 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x100c82 3 2 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x100c82 0x44 0xf2 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x100c85 [0xE8, 0x26, 0x59, 0x00, 0x00] (PushPre 0x100c85 5) (callEffect (fun _ => 0x1065b0) 0x100c8a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100c85 0x1065b0 0x100c8a).toInstrSpec (call_rel32_effect_step 0x100c85 0x5926 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c48) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c50) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c55) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c5d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c62) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c67) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c6f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c77) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c7a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c82) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c85) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 71), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065b0) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l100c40 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100c40 :=
  Rest.liftedBlock (rest_l100c40 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100c40 x hx)

theorem rest_l100c8a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100c8a bytes_l100c8a) (entryMap (live .l100c8a))
      18 0x100c8a bytes_l100c8a b_l100c8a := by
  have f0 : InstrSpec 0x100c8a [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x100c8a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100c8a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100c8a 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100c8a 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x100c8a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100c8f [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x100c8f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100c8f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100c8f 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100c8f 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x100c8f 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100c94 [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x100c94 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x100c94 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100c94 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100c94 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x100c94 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x100c9c [0x48, 0x8B, 0x54, 0x24, 0x20] (LoadPre 0x100c9c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100c9c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100c9c 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x100c9c 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x100c9c 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x100ca1 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x100ca1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100ca1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100ca1 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x100ca1 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x100ca1 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x100ca6 [0x48, 0x89, 0x44, 0x24, 0x48] (StorePre 0x100ca6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x100ca6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100ca6 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100ca6 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x100ca6 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x100cab [0x48, 0x89, 0x4C, 0x24, 0x50] (StorePre 0x100cab 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x100cab + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100cab 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100cab 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x100cab 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x100cb0 [0x48, 0x89, 0x74, 0x24, 0x58] (StorePre 0x100cb0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100cb0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100cb0 6 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100cb0 6 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x100cb0 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x100cb5 [0x48, 0x89, 0x54, 0x24, 0x60] (StorePre 0x100cb5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x100cb5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100cb5 2 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100cb5 2 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x100cb5 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x100cba [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100cba 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100cba + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100cba (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100cba (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100cba 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x100cc3 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100cc3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100cc3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100cc3 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100cc3 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100cc3 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x100ccc [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100ccc 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100ccc + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100ccc (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100ccc (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100ccc 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x100cd5 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100cd5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100cd5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100cd5 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100cd5 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100cd5 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x100cde [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100cde) (movR32Imm32Effect 0x100cde 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x100cde 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x100cde 0xbe (by decide) 0x4) pre_rip
  have f14 : InstrSpec 0x100ce3 [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100ce3) (movR32Imm32Effect 0x100ce3 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x100ce3 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x100ce3 0xb9 (by decide) 0x4) pre_rip
  have f15 : InstrSpec 0x100ce8 [0x48, 0x8D, 0x7C, 0x24, 0x48] (fun s => s.RIP = 0x100ce8) (leaR64Effect 0x100ce8 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x100ce8 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x100ce8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x100ced [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x100ced) (movR64R64Effect 0x100ced 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x100ced 2 12).toInstrSpec (mov_r64_r64_effect_step 0x100ced 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x100cf0 [0xE8, 0x5B, 0x72, 0x02, 0x00] (PushPre 0x100cf0 5) (callEffect (fun _ => 0x127f50) 0x100cf5)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100cf0 0x127f50 0x100cf5).toInstrSpec (call_rel32_effect_step 0x100cf0 0x2725b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c8f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c94) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c9c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ca1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ca6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cab) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cb0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cb5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cba) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cc3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ccc) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cd5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cde) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ce3) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 72), (2, 58), (3, 3), (4, 4), (5, 5), (6, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ce8) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 72), (2, 58), (3, 3), (4, 4), (5, 5), (6, 70), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ced) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 53), (1, 72), (2, 76), (3, 3), (4, 4), (5, 5), (6, 70), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cf0) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f17 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 53), (1, 72), (2, 76), (3, 3), (4, 78), (5, 5), (6, 70), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f50) f17 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 80) (by decide) (by decide) rfl rfl

theorem block_l100c8a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100c8a :=
  Rest.liftedBlock (rest_l100c8a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100c8a x hx)

theorem rest_l100cf5_3 [Bindings] (code : CodeMap) :
    Rest (n := 169) code lifted (codeRange 0x100cf5 bytes_l100cf5) [(0, 167), (1, 164), (2, 150), (3, 3), (4, 4), (5, 5), (6, 144), (7, 156), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x100dc6 bytes_l100cf5_3 b_l100cf5_3 := by
  have f60 : InstrSpec 0x100dc6 [0x24, 0x01] (fun s => s.RIP = 0x100dc6) (andAlImm8Effect 0x100dc6 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x100dc6 0x1).toInstrSpec (and_al_imm8_effect_step 0x100dc6 0x1) pre_rip
  have f61 : InstrSpec 0x100dc8 [0x88, 0x44, 0x24, 0x08] (StorePre 0x100dc8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100dc8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x100dc8 4 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x100dc8 4 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_effect_step 0x100dc8 0 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f62 : InstrSpec 0x100dcc [0x80, 0x7C, 0x24, 0x08, 0x00] (LoadPre 0x100dcc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100dcc + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x100dcc 5 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x100dcc 5 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x100dcc (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f60 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 169), (1, 164), (2, 150), (3, 3), (4, 4), (5, 5), (6, 144), (7, 156), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dc8) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.exec (n := 171) (ρ' := [(0, 169), (1, 164), (2, 150), (3, 3), (4, 4), (5, 5), (6, 144), (7, 156), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dcc) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f62 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 169), (1, 164), (2, 150), (3, 3), (4, 4), (5, 5), (6, 144), (7, 156), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 172), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dd1) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 174) (jcc_rel8_effect_step 0x100dd1 5 0x22) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l100cf5_2 [Bindings] (code : CodeMap) :
    Rest (n := 131) code lifted (codeRange 0x100cf5 bytes_l100cf5) [(0, 80), (1, 119), (2, 129), (3, 3), (4, 4), (5, 5), (6, 113), (7, 125), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      24 0x100d7e bytes_l100cf5_2 b_l100cf5_2 := by
  have f40 : InstrSpec 0x100d7e [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x100d7e) (orR64R64Effect 0x100d7e 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x100d7e 2 7).toInstrSpec (or_r64_r64_effect_step 0x100d7e 0x48 0xfa (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x100d81 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x100d81) (shrR64Effect 0x100d81 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x100d81 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x100d81 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x100d85 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x100d85 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100d85 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100d85 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100d85 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x100d85 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f43 : InstrSpec 0x100d8a [0x48, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x100d8a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100d8a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100d8a 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100d8a 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x100d8a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f44 : InstrSpec 0x100d8f [0x31, 0xD2] (fun s => s.RIP = 0x100d8f) (xorR32R32Effect 0x100d8f 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d8f 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x100d8f 0xd2 (by decide)) pre_rip
  have f45 : InstrSpec 0x100d91 [0x48, 0x29, 0xCA] (fun s => s.RIP = 0x100d91) (subR64R64Effect 0x100d91 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x100d91 2 1).toInstrSpec (sub_r64_r64_effect_step 0x100d91 0x48 0xca (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x100d94 [0x48, 0x8B, 0x4C, 0x24, 0x60] (LoadPre 0x100d94 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x100d94 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100d94 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100d94 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x100d94 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f47 : InstrSpec 0x100d99 [0x49, 0x8B, 0x77, 0x18] (LoadPre 0x100d99 (fun s => AddrMode.addr (.base 15 (.d8 0x18)) s (0x100d99 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100d99 6 (.base 15 (.d8 0x18)))
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x100d99 6 (.base 15 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x100d99 0x49 (by decide) 6 (.base 15 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f48 : InstrSpec 0x100d9d [0x48, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x100d9d) (sarR64Effect 0x100d9d 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (sarR64Effect_footprint 0x100d9d 4 2 63).toInstrSpec (sar_r64_imm8_effect_step 0x100d9d 0x48 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x100da1 [0x48, 0x01, 0xCA] (fun s => s.RIP = 0x100da1) (addR64R64Effect 0x100da1 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x100da1 2 1).toInstrSpec (add_r64_r64_effect_step 0x100da1 0x48 0xca (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x100da4 [0x48, 0x29, 0xF2] (fun s => s.RIP = 0x100da4) (subR64R64Effect 0x100da4 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x100da4 2 6).toInstrSpec (sub_r64_r64_effect_step 0x100da4 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x100da7 [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x100da7) (notR64Effect 0x100da7 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x100da7 1).toInstrSpec (not_r64_effect_step 0x100da7 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x100daa [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x100daa) (movR64R64Effect 0x100daa 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x100daa 7 6).toInstrSpec (mov_r64_r64_effect_step 0x100daa 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x100dad [0x48, 0x21, 0xCF] (fun s => s.RIP = 0x100dad) (andR64R64Effect 0x100dad 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100dad 7 1).toInstrSpec (and_r64_r64_effect_step 0x100dad 0x48 0xcf (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x100db0 [0x48, 0x09, 0xF1] (fun s => s.RIP = 0x100db0) (orR64R64Effect 0x100db0 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x100db0 1 6).toInstrSpec (or_r64_r64_effect_step 0x100db0 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x100db3 [0x48, 0x21, 0xD1] (fun s => s.RIP = 0x100db3) (andR64R64Effect 0x100db3 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100db3 1 2).toInstrSpec (and_r64_r64_effect_step 0x100db3 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x100db6 [0x48, 0x09, 0xF9] (fun s => s.RIP = 0x100db6) (orR64R64Effect 0x100db6 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x100db6 1 7).toInstrSpec (or_r64_r64_effect_step 0x100db6 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x100db9 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x100db9) (shrR64Effect 0x100db9 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x100db9 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x100db9 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x100dbd [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x100dbd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100dbd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100dbd 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100dbd 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x100dbd 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f59 : InstrSpec 0x100dc2 [0x22, 0x44, 0x24, 0x08] (LoadPre 0x100dc2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100dc2 + BitVec.ofNat 64 4)) 1) (andR8M8Effect 0x100dc2 4 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (andR8M8Effect_footprint 0x100dc2 4 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (and_r8_m8_effect_step 0x100dc2 0 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f40 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 80), (1, 119), (2, 131), (3, 3), (4, 4), (5, 5), (6, 113), (7, 125), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d81) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f41 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 80), (1, 119), (2, 133), (3, 3), (4, 4), (5, 5), (6, 113), (7, 125), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d85) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.exec (n := 135) (ρ' := [(0, 80), (1, 119), (2, 133), (3, 3), (4, 4), (5, 5), (6, 113), (7, 125), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d8a) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f43 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 80), (1, 136), (2, 133), (3, 3), (4, 4), (5, 5), (6, 113), (7, 125), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d8f) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f44 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 80), (1, 136), (2, 138), (3, 3), (4, 4), (5, 5), (6, 113), (7, 125), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d91) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f45 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 80), (1, 136), (2, 140), (3, 3), (4, 4), (5, 5), (6, 113), (7, 125), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d94) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 80), (1, 142), (2, 140), (3, 3), (4, 4), (5, 5), (6, 113), (7, 125), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d99) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f47 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 80), (1, 142), (2, 140), (3, 3), (4, 4), (5, 5), (6, 144), (7, 125), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d9d) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f48 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 80), (1, 142), (2, 146), (3, 3), (4, 4), (5, 5), (6, 144), (7, 125), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100da1) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f49 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 80), (1, 142), (2, 148), (3, 3), (4, 4), (5, 5), (6, 144), (7, 125), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100da4) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f50 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 80), (1, 142), (2, 150), (3, 3), (4, 4), (5, 5), (6, 144), (7, 125), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100da7) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f51 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 80), (1, 152), (2, 150), (3, 3), (4, 4), (5, 5), (6, 144), (7, 125), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100daa) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f52 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 80), (1, 152), (2, 150), (3, 3), (4, 4), (5, 5), (6, 144), (7, 154), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dad) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f53 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 80), (1, 152), (2, 150), (3, 3), (4, 4), (5, 5), (6, 144), (7, 156), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100db0) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f54 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 80), (1, 158), (2, 150), (3, 3), (4, 4), (5, 5), (6, 144), (7, 156), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100db3) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f55 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 80), (1, 160), (2, 150), (3, 3), (4, 4), (5, 5), (6, 144), (7, 156), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100db6) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f56 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 80), (1, 162), (2, 150), (3, 3), (4, 4), (5, 5), (6, 144), (7, 156), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100db9) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f57 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 80), (1, 164), (2, 150), (3, 3), (4, 4), (5, 5), (6, 144), (7, 156), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dbd) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.exec (n := 166) (ρ' := [(0, 80), (1, 164), (2, 150), (3, 3), (4, 4), (5, 5), (6, 144), (7, 156), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dc2) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f59 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 167), (1, 164), (2, 150), (3, 3), (4, 4), (5, 5), (6, 144), (7, 156), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dc6) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100cf5_3 code

theorem rest_l100cf5_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x100cf5 bytes_l100cf5) [(0, 80), (1, 90), (2, 82), (3, 3), (4, 4), (5, 5), (6, 84), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      44 0x100d3a bytes_l100cf5_1 b_l100cf5_1 := by
  have f20 : InstrSpec 0x100d3a [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x100d3a) (notR64Effect 0x100d3a 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x100d3a 2).toInstrSpec (not_r64_effect_step 0x100d3a 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x100d3d [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x100d3d) (movR64R64Effect 0x100d3d 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x100d3d 7 6).toInstrSpec (mov_r64_r64_effect_step 0x100d3d 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x100d40 [0x48, 0x21, 0xD7] (fun s => s.RIP = 0x100d40) (andR64R64Effect 0x100d40 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100d40 7 2).toInstrSpec (and_r64_r64_effect_step 0x100d40 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x100d43 [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x100d43) (orR64R64Effect 0x100d43 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x100d43 2 6).toInstrSpec (or_r64_r64_effect_step 0x100d43 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x100d46 [0x48, 0x21, 0xCA] (fun s => s.RIP = 0x100d46) (andR64R64Effect 0x100d46 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100d46 2 1).toInstrSpec (and_r64_r64_effect_step 0x100d46 0x48 0xca (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x100d49 [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x100d49) (orR64R64Effect 0x100d49 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x100d49 2 7).toInstrSpec (or_r64_r64_effect_step 0x100d49 0x48 0xfa (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x100d4c [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x100d4c) (shrR64Effect 0x100d4c 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x100d4c 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x100d4c 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x100d50 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x100d50 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100d50 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100d50 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100d50 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x100d50 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x100d55 [0x31, 0xC9] (fun s => s.RIP = 0x100d55) (xorR32R32Effect 0x100d55 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d55 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x100d55 0xc9 (by decide)) pre_rip
  have f29 : InstrSpec 0x100d57 [0x48, 0x2B, 0x4C, 0x24, 0x08] (LoadPre 0x100d57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100d57 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x100d57 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x100d57 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x100d57 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x100d5c [0x48, 0x8B, 0x54, 0x24, 0x58] (LoadPre 0x100d5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100d5c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100d5c 2 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x100d5c 2 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x100d5c 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x100d61 [0x49, 0x8B, 0x77, 0x10] (LoadPre 0x100d61 (fun s => AddrMode.addr (.base 15 (.d8 0x10)) s (0x100d61 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100d61 6 (.base 15 (.d8 0x10)))
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x100d61 6 (.base 15 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x100d61 0x49 (by decide) 6 (.base 15 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x100d65 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x100d65) (sarR64Effect 0x100d65 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x100d65 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x100d65 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x100d69 [0x48, 0x01, 0xD1] (fun s => s.RIP = 0x100d69) (addR64R64Effect 0x100d69 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x100d69 1 2).toInstrSpec (add_r64_r64_effect_step 0x100d69 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x100d6c [0x48, 0x29, 0xF1] (fun s => s.RIP = 0x100d6c) (subR64R64Effect 0x100d6c 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x100d6c 1 6).toInstrSpec (sub_r64_r64_effect_step 0x100d6c 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x100d6f [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x100d6f) (notR64Effect 0x100d6f 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x100d6f 2).toInstrSpec (not_r64_effect_step 0x100d6f 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x100d72 [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x100d72) (movR64R64Effect 0x100d72 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x100d72 7 6).toInstrSpec (mov_r64_r64_effect_step 0x100d72 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x100d75 [0x48, 0x21, 0xD7] (fun s => s.RIP = 0x100d75) (andR64R64Effect 0x100d75 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100d75 7 2).toInstrSpec (and_r64_r64_effect_step 0x100d75 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x100d78 [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x100d78) (orR64R64Effect 0x100d78 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x100d78 2 6).toInstrSpec (or_r64_r64_effect_step 0x100d78 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x100d7b [0x48, 0x21, 0xCA] (fun s => s.RIP = 0x100d7b) (andR64R64Effect 0x100d7b 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100d7b 2 1).toInstrSpec (and_r64_r64_effect_step 0x100d7b 0x48 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 80), (1, 90), (2, 92), (3, 3), (4, 4), (5, 5), (6, 84), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d3d) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f21 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 80), (1, 90), (2, 92), (3, 3), (4, 4), (5, 5), (6, 84), (7, 94), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d40) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f22 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 80), (1, 90), (2, 92), (3, 3), (4, 4), (5, 5), (6, 84), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d43) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f23 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 80), (1, 90), (2, 98), (3, 3), (4, 4), (5, 5), (6, 84), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d46) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f24 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 80), (1, 90), (2, 100), (3, 3), (4, 4), (5, 5), (6, 84), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d49) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f25 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 80), (1, 90), (2, 102), (3, 3), (4, 4), (5, 5), (6, 84), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d4c) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f26 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 80), (1, 90), (2, 104), (3, 3), (4, 4), (5, 5), (6, 84), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d50) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 80), (1, 90), (2, 104), (3, 3), (4, 4), (5, 5), (6, 84), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d55) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f28 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 80), (1, 107), (2, 104), (3, 3), (4, 4), (5, 5), (6, 84), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d57) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f29 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 80), (1, 109), (2, 104), (3, 3), (4, 4), (5, 5), (6, 84), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d5c) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f30 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 80), (1, 109), (2, 111), (3, 3), (4, 4), (5, 5), (6, 84), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d61) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f31 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 80), (1, 109), (2, 111), (3, 3), (4, 4), (5, 5), (6, 113), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d65) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f32 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 80), (1, 115), (2, 111), (3, 3), (4, 4), (5, 5), (6, 113), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d69) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f33 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 80), (1, 117), (2, 111), (3, 3), (4, 4), (5, 5), (6, 113), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d6c) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f34 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 80), (1, 119), (2, 111), (3, 3), (4, 4), (5, 5), (6, 113), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d6f) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f35 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 80), (1, 119), (2, 121), (3, 3), (4, 4), (5, 5), (6, 113), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d72) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f36 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 80), (1, 119), (2, 121), (3, 3), (4, 4), (5, 5), (6, 113), (7, 123), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d75) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f37 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 80), (1, 119), (2, 121), (3, 3), (4, 4), (5, 5), (6, 113), (7, 125), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d78) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f38 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 80), (1, 119), (2, 127), (3, 3), (4, 4), (5, 5), (6, 113), (7, 125), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d7b) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f39 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 80), (1, 119), (2, 129), (3, 3), (4, 4), (5, 5), (6, 113), (7, 125), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d7e) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100cf5_2 code

theorem rest_l100cf5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100cf5 bytes_l100cf5) (entryMap (live .l100cf5))
      64 0x100cf5 bytes_l100cf5 b_l100cf5 := by
  have f0 : InstrSpec 0x100cf5 [0x48, 0x8B, 0x4C, 0x24, 0x48] (LoadPre 0x100cf5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x100cf5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100cf5 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100cf5 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x100cf5 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100cfa [0x49, 0x8B, 0x17] (LoadPre 0x100cfa (fun s => AddrMode.addr (.base 15 .none) s (0x100cfa + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100cfa 2 (.base 15 .none))
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x100cfa 2 (.base 15 .none)).toInstrSpec (mov_r64_m64_effect_step 0x100cfa 0x49 (by decide) 2 (.base 15 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100cfd [0x48, 0x89, 0xCE] (fun s => s.RIP = 0x100cfd) (movR64R64Effect 0x100cfd 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100cfd 6 1).toInstrSpec (mov_r64_r64_effect_step 0x100cfd 0x48 0xce (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100d00 [0x48, 0x29, 0xD6] (fun s => s.RIP = 0x100d00) (subR64R64Effect 0x100d00 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (subR64R64Effect_footprint 0x100d00 6 2).toInstrSpec (sub_r64_r64_effect_step 0x100d00 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100d03 [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x100d03) (notR64Effect 0x100d03 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x100d03 1).toInstrSpec (not_r64_effect_step 0x100d03 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x100d06 [0x48, 0x89, 0xD7] (fun s => s.RIP = 0x100d06) (movR64R64Effect 0x100d06 7 2)
      [.gpr 2] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x100d06 7 2).toInstrSpec (mov_r64_r64_effect_step 0x100d06 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100d09 [0x48, 0x21, 0xCF] (fun s => s.RIP = 0x100d09) (andR64R64Effect 0x100d09 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100d09 7 1).toInstrSpec (and_r64_r64_effect_step 0x100d09 0x48 0xcf (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100d0c [0x48, 0x09, 0xD1] (fun s => s.RIP = 0x100d0c) (orR64R64Effect 0x100d0c 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x100d0c 1 2).toInstrSpec (or_r64_r64_effect_step 0x100d0c 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100d0f [0x48, 0x21, 0xF1] (fun s => s.RIP = 0x100d0f) (andR64R64Effect 0x100d0f 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100d0f 1 6).toInstrSpec (and_r64_r64_effect_step 0x100d0f 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x100d12 [0x48, 0x09, 0xF9] (fun s => s.RIP = 0x100d12) (orR64R64Effect 0x100d12 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x100d12 1 7).toInstrSpec (or_r64_r64_effect_step 0x100d12 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x100d15 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x100d15) (shrR64Effect 0x100d15 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x100d15 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x100d15 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x100d19 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x100d19 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100d19 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100d19 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100d19 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x100d19 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x100d1e [0x31, 0xC9] (fun s => s.RIP = 0x100d1e) (xorR32R32Effect 0x100d1e 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d1e 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x100d1e 0xc9 (by decide)) pre_rip
  have f13 : InstrSpec 0x100d20 [0x48, 0x2B, 0x4C, 0x24, 0x08] (LoadPre 0x100d20 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100d20 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x100d20 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x100d20 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x100d20 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x100d25 [0xF6, 0xD0] (fun s => s.RIP = 0x100d25) (notR8Effect 0x100d25 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR8Effect_footprint 0x100d25 2 0).toInstrSpec (not_r8_effect_step 0x100d25 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x100d27 [0x48, 0x8B, 0x54, 0x24, 0x50] (LoadPre 0x100d27 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x100d27 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100d27 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x100d27 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x100d27 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x100d2c [0x49, 0x8B, 0x77, 0x08] (LoadPre 0x100d2c (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x100d2c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100d2c 6 (.base 15 (.d8 0x8)))
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x100d2c 6 (.base 15 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x100d2c 0x49 (by decide) 6 (.base 15 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x100d30 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x100d30) (sarR64Effect 0x100d30 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x100d30 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x100d30 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x100d34 [0x48, 0x01, 0xD1] (fun s => s.RIP = 0x100d34) (addR64R64Effect 0x100d34 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x100d34 1 2).toInstrSpec (add_r64_r64_effect_step 0x100d34 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x100d37 [0x48, 0x29, 0xF1] (fun s => s.RIP = 0x100d37) (subR64R64Effect 0x100d37 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x100d37 1 6).toInstrSpec (sub_r64_r64_effect_step 0x100d37 0x48 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cfa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cfd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d00) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d03) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d06) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d09) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d0c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d0f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 69), (2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d12) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d15) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 73), (2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d19) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 73), (2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d1e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 76), (2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d20) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 78), (2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d25) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 78), (2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d27) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 80), (1, 78), (2, 82), (3, 3), (4, 4), (5, 5), (6, 59), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d2c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 80), (1, 78), (2, 82), (3, 3), (4, 4), (5, 5), (6, 84), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d30) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 80), (1, 86), (2, 82), (3, 3), (4, 4), (5, 5), (6, 84), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d34) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 80), (1, 88), (2, 82), (3, 3), (4, 4), (5, 5), (6, 84), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d37) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 80), (1, 90), (2, 82), (3, 3), (4, 4), (5, 5), (6, 84), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d3a) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100cf5_1 code

theorem block_l100cf5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100cf5 :=
  Rest.liftedBlock (rest_l100cf5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100cf5 x hx)

theorem rest_l100dd3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100dd3 bytes_l100dd3) (entryMap (live .l100dd3))
      5 0x100dd3 bytes_l100dd3 b_l100dd3 := by
  have f0 : InstrSpec 0x100dd3 [0x48, 0x8B, 0x7C, 0x24, 0x40] (LoadPre 0x100dd3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100dd3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100dd3 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x100dd3 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x100dd3 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100dd8 [0x4D, 0x85, 0xED] (fun s => s.RIP = 0x100dd8) (testR64R64Effect 0x100dd8 13 13)
      [.gpr 13, .gpr 13] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x100dd8 13 13).toInstrSpec (test_r64_r64_effect_step 0x100dd8 0x4d 0xed (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100ddb [0x4C, 0x8B, 0xA4, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x100ddb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x100ddb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100ddb 12 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x100ddb 12 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x100ddb 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x100de3 [0x48, 0x8D, 0x1D, 0x36, 0x9A, 0x02, 0x00] (fun s => s.RIP = 0x100de3) (leaR64Effect 0x100de3 3 (.rip 0x29a36))
      [] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x100de3 3 (.rip 0x29a36)).toInstrSpec (lea_r64_effect_step 0x100de3 0x48 (by decide) 3 (.rip 0x29a36) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dd8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ddb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100de3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 59), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dea) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel32_effect_step 0x100dea 5 0xfffffcc0) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100dd3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100dd3 :=
  Rest.liftedBlock (rest_l100dd3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100dd3 x hx)

theorem rest_l100df0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100df0 bytes_l100df0) (entryMap (live .l100df0))
      1 0x100df0 bytes_l100df0 b_l100df0 := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x100df0 0xfffffcfa (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100df0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100df0 :=
  Rest.liftedBlock (rest_l100df0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100df0 x hx)

theorem rest_l100df5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100df5 bytes_l100df5) (entryMap (live .l100df5))
      5 0x100df5 bytes_l100df5 b_l100df5 := by
  have f0 : InstrSpec 0x100df5 [0x48, 0x8D, 0x7C, 0x24, 0x48] (fun s => s.RIP = 0x100df5) (leaR64Effect 0x100df5 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x100df5 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x100df5 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100dfa [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x100dfa) (movR64R64Effect 0x100dfa 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100dfa 6 15).toInstrSpec (mov_r64_r64_effect_step 0x100dfa 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100dfd [0x48, 0x8B, 0x54, 0x24, 0x28] (LoadPre 0x100dfd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100dfd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100dfd 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x100dfd 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x100dfd 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x100e02 [0x4C, 0x89, 0xE9] (fun s => s.RIP = 0x100e02) (movR64R64Effect 0x100e02 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x100e02 1 13).toInstrSpec (mov_r64_r64_effect_step 0x100e02 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100e05 [0xE8, 0xF6, 0xF1, 0xFF, 0xFF] (PushPre 0x100e05 5) (callEffect (fun _ => 0x100000) 0x100e0a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100e05 0x100000 0x100e0a).toInstrSpec (call_rel32_effect_step 0x100e05 0xfffff1f6 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dfa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dfd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e02) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e05) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 59), (2, 57), (3, 3), (4, 61), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100000) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l100df5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100df5 :=
  Rest.liftedBlock (rest_l100df5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100df5 x hx)

theorem rest_l100e0a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100e0a bytes_l100e0a) (entryMap (live .l100e0a))
      8 0x100e0a bytes_l100e0a b_l100e0a := by
  have f0 : InstrSpec 0x100e0a [0x48, 0x81, 0xC4, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100e0a) (addR64Imm32Effect 0x100e0a 4 0xb8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x100e0a 4 0xb8).toInstrSpec (add_r64_imm32_effect_step 0x100e0a 0x48 0xc4 0xb8 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100e11 [0x5B] (PopPre 0x100e11) (popR64Effect 0x100e11 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100e11 1 3).toInstrSpec (pop_r64_effect_step 0x100e11 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x100e12 [0x41, 0x5C] (PopPre 0x100e12) (popR64Effect 0x100e12 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100e12 2 12).toInstrSpec (pop_r64_rex_effect_step 0x100e12 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x100e14 [0x41, 0x5D] (PopPre 0x100e14) (popR64Effect 0x100e14 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100e14 2 13).toInstrSpec (pop_r64_rex_effect_step 0x100e14 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x100e16 [0x41, 0x5E] (PopPre 0x100e16) (popR64Effect 0x100e16 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100e16 2 14).toInstrSpec (pop_r64_rex_effect_step 0x100e16 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x100e18 [0x41, 0x5F] (PopPre 0x100e18) (popR64Effect 0x100e18 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100e18 2 15).toInstrSpec (pop_r64_rex_effect_step 0x100e18 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x100e1a [0x5D] (PopPre 0x100e1a) (popR64Effect 0x100e1a 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100e1a 1 5).toInstrSpec (pop_r64_effect_step 0x100e1a 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x100e1b [0xC3] (RetPre 0x100e1b) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x100e1b).toInstrSpec (ret_effect_step 0x100e1b) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e11) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e12) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e14) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e16) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e18) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e1a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e1b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l100e0a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100e0a :=
  Rest.liftedBlock (rest_l100e0a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100e0a x hx)

theorem rest_l100e1c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100e1c bytes_l100e1c) (entryMap (live .l100e1c))
      4 0x100e1c bytes_l100e1c b_l100e1c := by
  have f0 : InstrSpec 0x100e1c [0x31, 0xFF] (fun s => s.RIP = 0x100e1c) (xorR32R32Effect 0x100e1c 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100e1c 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x100e1c 0xff (by decide)) pre_rip
  have f1 : InstrSpec 0x100e1e [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x100e1e) (movR64R64Effect 0x100e1e 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x100e1e 2 13).toInstrSpec (mov_r64_r64_effect_step 0x100e1e 0x4c 0xea (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100e21 [0x48, 0xC7, 0xC1, 0x80, 0x20, 0x20, 0x00] (fun s => s.RIP = 0x100e21) (movR64Imm32Effect 0x100e21 1 0x202080)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x100e21 1 0x202080).toInstrSpec (mov_r64_imm32_effect_step 0x100e21 0x48 0xc1 (by decide) (by decide) (by decide) 0x202080) pre_rip
  have f3 : InstrSpec 0x100e28 [0xE8, 0x33, 0x8D, 0x02, 0x00] (PushPre 0x100e28 5) (callEffect (fun _ => 0x129b60) 0x100e2d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100e28 0x129b60 0x100e2d).toInstrSpec (call_rel32_effect_step 0x100e28 0x28d33 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 53), (13, 13)]) (p' := 0x100e1e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (4, 4), (5, 5), (6, 6), (7, 53), (13, 13)]) (p' := 0x100e21) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (2, 55), (4, 4), (5, 5), (6, 6), (7, 53), (13, 13)]) (p' := 0x100e28) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 57), (2, 55), (4, 59), (5, 5), (6, 6), (7, 53), (13, 13)]) (p' := 0x129b60) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l100e1c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100e1c :=
  Rest.liftedBlock (rest_l100e1c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100e1c x hx)

theorem rest_l100e2d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100e2d bytes_l100e2d) (entryMap (live .l100e2d))
      9 0x100e2d bytes_l100e2d b_l100e2d := by
  have f0 : InstrSpec 0x100e2d [0x48, 0xC7, 0x44, 0x24, 0x08, 0x98, 0x24, 0x20, 0x00] (StorePre 0x100e2d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100e2d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100e2d (.sib 4 none 0 (.d8 0x8)) 0x202498)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100e2d (.sib 4 none 0 (.d8 0x8)) 0x202498).toInstrSpec (mov_m64_imm32_effect_step 0x100e2d 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x202498) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x100e36 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x90, 0xA1, 0x12, 0x00] (StorePre 0x100e36 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100e36 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100e36 (.sib 4 none 0 (.d8 0x10)) 0x12a190)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100e36 (.sib 4 none 0 (.d8 0x10)) 0x12a190).toInstrSpec (mov_m64_imm32_effect_step 0x100e36 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x12a190) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x100e3f [0x48, 0x8D, 0x44, 0x24, 0x3C] (fun s => s.RIP = 0x100e3f) (leaR64Effect 0x100e3f 0 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x100e3f 0 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (lea_r64_effect_step 0x100e3f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100e44 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x100e44 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100e44 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100e44 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100e44 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x100e44 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x100e49 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x90, 0xA1, 0x12, 0x00] (StorePre 0x100e49 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100e49 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100e49 (.sib 4 none 0 (.d8 0x20)) 0x12a190)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100e49 (.sib 4 none 0 (.d8 0x20)) 0x12a190).toInstrSpec (mov_m64_imm32_effect_step 0x100e49 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x12a190) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x100e52 [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x100e52) (leaR64Effect 0x100e52 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x100e52 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x100e52 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100e57 [0x48, 0xC7, 0xC7, 0x8F, 0x02, 0x20, 0x00] (fun s => s.RIP = 0x100e57) (movR64Imm32Effect 0x100e57 7 0x20028f)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x100e57 7 0x20028f).toInstrSpec (mov_r64_imm32_effect_step 0x100e57 0x48 0xc7 (by decide) (by decide) (by decide) 0x20028f) pre_rip
  have f7 : InstrSpec 0x100e5e [0x48, 0xC7, 0xC2, 0xA0, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x100e5e) (movR64Imm32Effect 0x100e5e 2 0x2022a0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x100e5e 2 0x2022a0).toInstrSpec (mov_r64_imm32_effect_step 0x100e5e 0x48 0xc2 (by decide) (by decide) (by decide) 0x2022a0) pre_rip
  have f8 : InstrSpec 0x100e65 [0xE8, 0x06, 0x89, 0x02, 0x00] (PushPre 0x100e65 5) (callEffect (fun _ => 0x129770) 0x100e6a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100e65 0x129770 0x100e6a).toInstrSpec (call_rel32_effect_step 0x100e65 0x28906 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x100e36) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5)]) (p' := 0x100e3f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (4, 4), (5, 5)]) (p' := 0x100e44) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (4, 4), (5, 5)]) (p' := 0x100e49) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (4, 4), (5, 5)]) (p' := 0x100e52) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (4, 4), (5, 5), (6, 59)]) (p' := 0x100e57) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (4, 4), (5, 5), (6, 59), (7, 61)]) (p' := 0x100e5e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (2, 63), (4, 4), (5, 5), (6, 59), (7, 61)]) (p' := 0x100e65) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (2, 63), (4, 65), (5, 5), (6, 59), (7, 61)]) (p' := 0x129770) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l100e2d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100e2d :=
  Rest.liftedBlock (rest_l100e2d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100e2d x hx)

theorem rest_l100e6a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100e6a bytes_l100e6a) (entryMap (live .l100e6a))
      5 0x100e6a bytes_l100e6a b_l100e6a := by
  have f0 : InstrSpec 0x100e6a [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x100e6a) (movR64R64Effect 0x100e6a 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x100e6a 3 7).toInstrSpec (mov_r64_r64_effect_step 0x100e6a 0x48 0xfb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100e6d [0x48, 0x89, 0xCF] (fun s => s.RIP = 0x100e6d) (movR64R64Effect 0x100e6d 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x100e6d 7 1).toInstrSpec (mov_r64_r64_effect_step 0x100e6d 0x48 0xcf (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100e70 [0x48, 0x8B, 0x74, 0x24, 0x28] (LoadPre 0x100e70 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100e70 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100e70 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x100e70 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x100e70 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x100e75 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x100e75) (movR64R64Effect 0x100e75 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x100e75 2 13).toInstrSpec (mov_r64_r64_effect_step 0x100e75 0x4c 0xea (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100e78 [0xE8, 0x43, 0x30, 0x00, 0x00] (PushPre 0x100e78 5) (callEffect (fun _ => 0x103ec0) 0x100e7d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100e78 0x103ec0 0x100e7d).toInstrSpec (call_rel32_effect_step 0x100e78 0x3043 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e6d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e70) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e75) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 53), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e78) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 53), (4, 61), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ec0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l100e6a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100e6a :=
  Rest.liftedBlock (rest_l100e6a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100e6a x hx)

theorem rest_l100e7d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100e7d bytes_l100e7d) (entryMap (live .l100e7d))
      2 0x100e7d bytes_l100e7d b_l100e7d := by
  have f0 : InstrSpec 0x100e7d [0x48, 0x8B, 0x3B] (LoadPre 0x100e7d (fun s => AddrMode.addr (.base 3 .none) s (0x100e7d + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100e7d 7 (.base 3 .none))
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x100e7d 7 (.base 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x100e7d 0x48 (by decide) 7 (.base 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100e80 [0xE8, 0x2B, 0x59, 0x00, 0x00] (PushPre 0x100e80 5) (callEffect (fun _ => 0x1067b0) 0x100e85)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100e80 0x1067b0 0x100e85).toInstrSpec (call_rel32_effect_step 0x100e80 0x592b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e80) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (7, 53), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067b0) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l100e7d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100e7d :=
  Rest.liftedBlock (rest_l100e7d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100e7d x hx)

theorem rest_l100e85 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100e85 bytes_l100e85) (entryMap (live .l100e85))
      4 0x100e85 bytes_l100e85 b_l100e85 := by
  have f0 : InstrSpec 0x100e85 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100e85) (movR32Imm32Effect 0x100e85 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x100e85 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x100e85 0xbe (by decide) 0x8) pre_rip
  have f1 : InstrSpec 0x100e8a [0x48, 0xC7, 0xC7, 0x98, 0x20, 0x20, 0x00] (fun s => s.RIP = 0x100e8a) (movR64Imm32Effect 0x100e8a 7 0x202098)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x100e8a 7 0x202098).toInstrSpec (mov_r64_imm32_effect_step 0x100e8a 0x48 0xc7 (by decide) (by decide) (by decide) 0x202098) pre_rip
  have f2 : InstrSpec 0x100e91 [0x48, 0xC7, 0xC2, 0xC8, 0x20, 0x20, 0x00] (fun s => s.RIP = 0x100e91) (movR64Imm32Effect 0x100e91 2 0x2020c8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x100e91 2 0x2020c8).toInstrSpec (mov_r64_imm32_effect_step 0x100e91 0x48 0xc2 (by decide) (by decide) (by decide) 0x2020c8) pre_rip
  have f3 : InstrSpec 0x100e98 [0xE8, 0xC3, 0x86, 0x02, 0x00] (PushPre 0x100e98 5) (callEffect (fun _ => 0x129560) 0x100e9d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100e98 0x129560 0x100e9d).toInstrSpec (call_rel32_effect_step 0x100e98 0x286c3 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 53)]) (p' := 0x100e8a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x100e91) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x100e98) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)]) (p' := 0x129560) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l100e85 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100e85 :=
  Rest.liftedBlock (rest_l100e85 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100e85 x hx)

theorem rest_l100e9d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100e9d bytes_l100e9d) (entryMap (live .l100e9d))
      1 0x100e9d bytes_l100e9d b_l100e9d := by
  have f0 : InstrSpec 0x100e9d [0x0F, 0x1F, 0x00] (fun s => s.RIP = 0x100e9d) (fun _ => nopEffect 0x100e9d 3)
      [] [] [.rip] :=
    (nopEffect_footprint 0x100e9d 3).toInstrSpec (nop_m_effect_step 0x100e9d [] (by decide) (by decide) (.base 0 .none) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ea0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l100e9d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100e9d :=
  Rest.liftedBlock (rest_l100e9d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100e9d x hx)

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

theorem_by block_l100a40_eval :
    program.runBlock (dialect code) ⟨.l100a40, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100a6a_eval :
    program.runBlock (dialect code) ⟨.l100a6a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100aab_eval :
    program.runBlock (dialect code) ⟨.l100aab, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100ab0_eval :
    program.runBlock (dialect code) ⟨.l100ab0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100ac0_eval :
    program.runBlock (dialect code) ⟨.l100ac0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100ad7_eval :
    program.runBlock (dialect code) ⟨.l100ad7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100ae2_eval :
    program.runBlock (dialect code) ⟨.l100ae2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100aef_eval :
    program.runBlock (dialect code) ⟨.l100aef, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100afb_eval :
    program.runBlock (dialect code) ⟨.l100afb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100bc6_eval :
    program.runBlock (dialect code) ⟨.l100bc6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100bd9_eval :
    program.runBlock (dialect code) ⟨.l100bd9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100bf0_eval :
    program.runBlock (dialect code) ⟨.l100bf0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100bf8_eval :
    program.runBlock (dialect code) ⟨.l100bf8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100c38_eval :
    program.runBlock (dialect code) ⟨.l100c38, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100c40_eval :
    program.runBlock (dialect code) ⟨.l100c40, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100c8a_eval :
    program.runBlock (dialect code) ⟨.l100c8a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100cf5_eval :
    program.runBlock (dialect code) ⟨.l100cf5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100dd3_eval :
    program.runBlock (dialect code) ⟨.l100dd3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100df0_eval :
    program.runBlock (dialect code) ⟨.l100df0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100df5_eval :
    program.runBlock (dialect code) ⟨.l100df5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100e0a_eval :
    program.runBlock (dialect code) ⟨.l100e0a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100e1c_eval :
    program.runBlock (dialect code) ⟨.l100e1c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100e2d_eval :
    program.runBlock (dialect code) ⟨.l100e2d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100e6a_eval :
    program.runBlock (dialect code) ⟨.l100e6a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100e7d_eval :
    program.runBlock (dialect code) ⟨.l100e7d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100e85_eval :
    program.runBlock (dialect code) ⟨.l100e85, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100e9d_eval :
    program.runBlock (dialect code) ⟨.l100e9d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
