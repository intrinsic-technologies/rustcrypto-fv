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

theorem rest_l103670 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103670 bytes_l103670) (entryMap (live .l103670))
      12 0x103670 bytes_l103670 b_l103670 := by
  have f0 : InstrSpec 0x103670 [0x55] (PushPre 0x103670 1) (pushR64Effect 0x103670 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103670 1 5).toInstrSpec (push_r64_effect_step 0x103670 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x103671 [0x41, 0x57] (PushPre 0x103671 2) (pushR64Effect 0x103671 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103671 2 15).toInstrSpec (push_r64_rex_effect_step 0x103671 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x103673 [0x41, 0x56] (PushPre 0x103673 2) (pushR64Effect 0x103673 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103673 2 14).toInstrSpec (push_r64_rex_effect_step 0x103673 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x103675 [0x41, 0x55] (PushPre 0x103675 2) (pushR64Effect 0x103675 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103675 2 13).toInstrSpec (push_r64_rex_effect_step 0x103675 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x103677 [0x41, 0x54] (PushPre 0x103677 2) (pushR64Effect 0x103677 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103677 2 12).toInstrSpec (push_r64_rex_effect_step 0x103677 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x103679 [0x53] (PushPre 0x103679 1) (pushR64Effect 0x103679 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103679 1 3).toInstrSpec (push_r64_effect_step 0x103679 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10367a [0x48, 0x81, 0xEC, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10367a) (subR64Imm32Effect 0x10367a 4 0x88)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10367a 4 0x88).toInstrSpec (sub_r64_imm32_effect_step 0x10367a 0x48 0xec 0x88 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103681 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x103681) (movR64R64Effect 0x103681 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x103681 3 7).toInstrSpec (mov_r64_r64_effect_step 0x103681 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x103684 [0x44, 0x8B, 0x7E, 0x1C] (LoadPre 0x103684 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x103684 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x103684 15 (.base 6 (.d8 0x1c)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x103684 15 (.base 6 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x103684 0x44 (by decide) 7 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x103688 [0x8B, 0x6A, 0x08] (LoadPre 0x103688 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x103688 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x103688 5 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR32M32LowEffect_footprint 0x103688 5 (.base 2 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x103688 5 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x10368b [0x44, 0x01, 0xFD] (fun s => s.RIP = 0x10368b) (addR32R32Effect 0x10368b 3 5 15)
      [.gpr 5, .gpr 15] [] [.reg 5, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10368b 3 5 15).toInstrSpec (add_r32_r32_rex_effect_step 0x10368b 0x44 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103671) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103673) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103675) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103677) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103679) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10367a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103681) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103684) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103688) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10368b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10368e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 76) (jcc_rel32_effect_step 0x10368e 2 0x20c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103670 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103670 :=
  Rest.liftedBlock (rest_l103670 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103670 x hx)

theorem rest_l103694 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103694 bytes_l103694) (entryMap (live .l103694))
      9 0x103694 bytes_l103694 b_l103694 := by
  have f0 : InstrSpec 0x103694 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x103694) (movR64R64Effect 0x103694 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x103694 13 2).toInstrSpec (mov_r64_r64_effect_step 0x103694 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103697 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x103697) (movR64R64Effect 0x103697 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x103697 14 6).toInstrSpec (mov_r64_r64_effect_step 0x103697 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10369a [0x48, 0x8B, 0x36] (LoadPre 0x10369a (fun s => AddrMode.addr (.base 6 .none) s (0x10369a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10369a 6 (.base 6 .none))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10369a 6 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10369a 0x48 (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10369d [0x4D, 0x8B, 0x66, 0x08] (LoadPre 0x10369d (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x10369d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10369d 12 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x10369d 12 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10369d 0x4d (by decide) 4 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1036a1 [0x48, 0x8D, 0x7C, 0x24, 0x30] (fun s => s.RIP = 0x1036a1) (leaR64Effect 0x1036a1 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1036a1 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x1036a1 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1036a6 [0x48, 0x89, 0x74, 0x24, 0x68] (StorePre 0x1036a6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1036a6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1036a6 6 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1036a6 6 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x1036a6 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1036ab [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x1036ab) (movR64R64Effect 0x1036ab 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1036ab 2 12).toInstrSpec (mov_r64_r64_effect_step 0x1036ab 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1036ae [0x89, 0xE9] (fun s => s.RIP = 0x1036ae) (movR32R32Effect 0x1036ae 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1036ae 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x1036ae 0xe9 (by decide)) pre_rip
  have f8 : InstrSpec 0x1036b0 [0xE8, 0x9B, 0x45, 0x02, 0x00] (PushPre 0x1036b0 5) (callEffect (fun _ => 0x127c50) 0x1036b5)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1036b0 0x127c50 0x1036b5).toInstrSpec (call_rel32_effect_step 0x1036b0 0x2459b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103697) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10369a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10369d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036a1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036a6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036ab) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 64), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036ae) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036b0) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 68), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c50) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 70) (by decide) (by decide) rfl rfl

theorem block_l103694 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103694 :=
  Rest.liftedBlock (rest_l103694 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103694 x hx)

theorem rest_l1036b5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1036b5 bytes_l1036b5) (entryMap (live .l1036b5))
      3 0x1036b5 bytes_l1036b5 b_l1036b5 := by
  have f0 : InstrSpec 0x1036b5 [0x8B, 0x54, 0x24, 0x30] (LoadPre 0x1036b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1036b5 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1036b5 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1036b5 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r32_m32_low_effect_step 0x1036b5 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1036b9 [0x83, 0xFA, 0x02] (fun s => s.RIP = 0x1036b9) (cmpR32Imm8Effect 0x1036b9 3 2 0x2)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1036b9 3 2 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1036b9 0xfa 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036b9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036bc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1036bc 5 0x22) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1036b5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1036b5 :=
  Rest.liftedBlock (rest_l1036b5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1036b5 x hx)

theorem rest_l1036be [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1036be bytes_l1036be) (entryMap (live .l1036be))
      7 0x1036be bytes_l1036be b_l1036be := by
  have f0 : InstrSpec 0x1036be [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x1036be (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1036be + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1036be 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1036be 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1036be 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1036c3 [0x48, 0x8B, 0x4C, 0x24, 0x40] (LoadPre 0x1036c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1036c3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1036c3 1 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1036c3 1 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1036c3 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1036c8 [0x49, 0x89, 0x06] (StorePre 0x1036c8 3 (fun s => AddrMode.addr (.base 14 .none) s (0x1036c8 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1036c8 0 (.base 14 .none))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x1036c8 0 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1036c8 0x49 (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1036cb [0x49, 0x89, 0x4E, 0x08] (StorePre 0x1036cb 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1036cb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1036cb 1 (.base 14 (.d8 0x8)))
      [.gpr 1, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x1036cb 1 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1036cb 0x49 (by decide) 1 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1036cf [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x1036cf (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1036cf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1036cf 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1036cf 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1036cf 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1036d3 [0x48, 0x83, 0xF8, 0x3F] (fun s => s.RIP = 0x1036d3) (cmpR64Imm8Effect 0x1036d3 0 0x3f)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1036d3 0 0x3f).toInstrSpec (cmp_r64_imm8_effect_step 0x1036d3 0x48 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036c3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036c8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036cb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036cf) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036d3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036d7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x1036d7 6 0x4b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1036be [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1036be :=
  Rest.liftedBlock (rest_l1036be code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1036be x hx)

theorem rest_l1036d9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1036d9 bytes_l1036d9) (entryMap (live .l1036d9))
      2 0x1036d9 bytes_l1036d9 b_l1036d9 := by
  have f0 : InstrSpec 0x1036d9 [0xB8, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1036d9) (movR32Imm32Effect 0x1036d9 5 0 0x6)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1036d9 5 0 0x6).toInstrSpec (mov_r32_imm32_effect_step 0x1036d9 0xb8 (by decide) 0x6) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036de) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x1036de 0x60 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1036d9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1036d9 :=
  Rest.liftedBlock (rest_l1036d9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1036d9 x hx)

theorem rest_l1036e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1036e0 bytes_l1036e0) (entryMap (live .l1036e0))
      11 0x1036e0 bytes_l1036e0 b_l1036e0 := by
  have f0 : InstrSpec 0x1036e0 [0x8B, 0x4C, 0x24, 0x34] (LoadPre 0x1036e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x1036e0 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1036e0 1 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x1036e0 1 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r32_m32_low_effect_step 0x1036e0 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1036e4 [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x1036e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1036e4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1036e4 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1036e4 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1036e4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1036e9 [0x48, 0x8B, 0x74, 0x24, 0x40] (LoadPre 0x1036e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1036e9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1036e9 6 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1036e9 6 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1036e9 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1036ee [0x48, 0x8B, 0x7C, 0x24, 0x48] (LoadPre 0x1036ee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1036ee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1036ee 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1036ee 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x1036ee 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1036f3 [0x48, 0x89, 0x3C, 0x24] (StorePre 0x1036f3 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1036f3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1036f3 7 (.sib 4 none 0 .none))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1036f3 7 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1036f3 0x48 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1036f7 [0x48, 0x8B, 0x7C, 0x24, 0x50] (LoadPre 0x1036f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1036f7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1036f7 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1036f7 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x1036f7 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1036fc [0x48, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x1036fc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1036fc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1036fc 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1036fc 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1036fc 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x103701 [0x48, 0x8B, 0x7C, 0x24, 0x58] (LoadPre 0x103701 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x103701 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103701 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103701 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x103701 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x103706 [0x48, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x103706 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103706 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103706 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103706 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x103706 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10370b [0x48, 0x8B, 0x7C, 0x24, 0x60] (LoadPre 0x10370b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10370b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10370b 7 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10370b 7 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x10370b 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x103710 [0x48, 0x89, 0x7C, 0x24, 0x18] (StorePre 0x103710 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103710 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103710 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103710 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x103710 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036e4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036e9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036ee) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036f3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036f7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036fc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 62), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103701) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103706) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10370b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103710) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103715) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 71) (by decide) rfl

theorem block_l1036e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1036e0 :=
  Rest.liftedBlock (rest_l1036e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1036e0 x hx)

theorem rest_l103715 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103715 bytes_l103715) (entryMap (live .l103715))
      3 0x103715 bytes_l103715 b_l103715 := by
  have f0 : InstrSpec 0x103715 [0x48, 0xBF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x103715) (movR64Imm64Effect 0x103715 7 0xffffffff00000000)
      [] [] [.reg 7, .rip] :=
    (movR64Imm64Effect_footprint 0x103715 7 0xffffffff00000000).toInstrSpec (mov_r64_imm64_effect_step 0x103715 0x48 0xbf (by decide) (by decide) 0xffffffff00000000) pre_rip
  have f1 : InstrSpec 0x10371f [0x48, 0x21, 0xF7] (fun s => s.RIP = 0x10371f) (andR64R64Effect 0x10371f 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10371f 7 6).toInstrSpec (and_r64_r64_effect_step 0x10371f 0x48 0xf7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10371f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103722) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x103722 0x29 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103715 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103715 :=
  Rest.liftedBlock (rest_l103715 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103715 x hx)

theorem rest_l103724 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103724 bytes_l103724) (entryMap (live .l103724))
      5 0x103724 bytes_l103724 b_l103724 := by
  have f0 : InstrSpec 0x103724 [0x48, 0xFF, 0xC0] (fun s => s.RIP = 0x103724) (incR64Effect 0x103724 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (incR64Effect_footprint 0x103724 0).toInstrSpec (inc_r64_effect_step 0x103724 0x48 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103727 [0x49, 0x89, 0x46, 0x10] (StorePre 0x103727 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x103727 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103727 0 (.base 14 (.d8 0x10)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x103727 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x103727 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10372b [0x45, 0x8B, 0x7E, 0x18] (LoadPre 0x10372b (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x10372b + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x10372b 15 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x10372b 15 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x10372b 0x45 (by decide) 7 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10372f [0x44, 0x39, 0xFD] (fun s => s.RIP = 0x10372f) (cmpR32R32Effect 0x10372f 3 5 15)
      [.gpr 5, .gpr 15] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x10372f 3 5 15).toInstrSpec (cmp_r32_r32_rex_effect_step 0x10372f 0x44 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103727) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10372b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10372f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103732) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x103732 6 0x77) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103724 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103724 :=
  Rest.liftedBlock (rest_l103724 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103724 x hx)

theorem rest_l103734 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103734 bytes_l103734) (entryMap (live .l103734))
      3 0x103734 bytes_l103734 b_l103734 := by
  have f0 : InstrSpec 0x103734 [0x41, 0x8D, 0x47, 0x01] (fun s => s.RIP = 0x103734) (leaR32Effect 0x103734 4 0 (.base 15 (.d8 0x1)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (leaR32Effect_footprint 0x103734 4 0 (.base 15 (.d8 0x1))).toInstrSpec (lea_r32_rex_effect_step 0x103734 0x41 (by decide) 0 (.base 15 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103738 [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x103738) (shlR64Effect 0x103738 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x103738 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x103738 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10373c [0x48, 0x83, 0xC8, 0x03] (fun s => s.RIP = 0x10373c) (orR64Imm8Effect 0x10373c 0 0x3)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x10373c 0 0x3).toInstrSpec (or_r64_imm8_effect_step 0x10373c 0x48 0xc8 0x3 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103738) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10373c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103740) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l103734 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103734 :=
  Rest.liftedBlock (rest_l103734 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103734 x hx)

theorem rest_l103740 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103740 bytes_l103740) (entryMap (live .l103740))
      4 0x103740 bytes_l103740 b_l103740 := by
  have f0 : InstrSpec 0x103740 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103740) (movR32Imm32Effect 0x103740 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x103740 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x103740 0xba (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x103745 [0x31, 0xFF] (fun s => s.RIP = 0x103745) (xorR32R32Effect 0x103745 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103745 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x103745 0xff (by decide)) pre_rip
  have f2 : InstrSpec 0x103747 [0x44, 0x89, 0xF9] (fun s => s.RIP = 0x103747) (movR32R32Effect 0x103747 3 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x103747 3 1 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x103747 0x44 0xf9 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10374a [0x44, 0x89, 0xFE] (fun s => s.RIP = 0x10374a) (movR32R32Effect 0x10374a 3 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x10374a 3 6 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x10374a 0x44 0xfe (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103745) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (7, 55), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103747) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 53), (3, 3), (4, 4), (7, 55), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10374a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 57), (2, 53), (3, 3), (4, 4), (6, 59), (7, 55), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10374d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l103740 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103740 :=
  Rest.liftedBlock (rest_l103740 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103740 x hx)

theorem rest_l10374d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10374d bytes_l10374d) (entryMap (live .l10374d))
      18 0x10374d bytes_l10374d b_l10374d := by
  have f0 : InstrSpec 0x10374d [0x89, 0xF6] (fun s => s.RIP = 0x10374d) (movR32R32Effect 0x10374d 2 6 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x10374d 2 6 6).toInstrSpec (mov_r32_r32_effect_step 0x10374d 0xf6 (by decide)) pre_rip
  have f1 : InstrSpec 0x10374f [0x48, 0x09, 0xFE] (fun s => s.RIP = 0x10374f) (orR64R64Effect 0x10374f 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10374f 6 7).toInstrSpec (or_r64_r64_effect_step 0x10374f 0x48 0xfe (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103752 [0x48, 0x8B, 0x3C, 0x24] (LoadPre 0x103752 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x103752 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103752 7 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103752 7 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x103752 0x48 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x103756 [0x4C, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x103756 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103756 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103756 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x103756 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x103756 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10375b [0x4C, 0x89, 0x44, 0x24, 0x28] (StorePre 0x10375b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10375b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10375b 8 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10375b 8 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10375b 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x103760 [0x48, 0x89, 0x7C, 0x24, 0x20] (StorePre 0x103760 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103760 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103760 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103760 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x103760 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x103765 [0x48, 0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x103765 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103765 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103765 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103765 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x103765 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10376a [0x48, 0x89, 0x7B, 0x30] (StorePre 0x10376a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x10376a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10376a 7 (.base 3 (.d8 0x30)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10376a 7 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10376a 0x48 (by decide) 7 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10376e [0x48, 0x8B, 0x7C, 0x24, 0x10] (LoadPre 0x10376e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10376e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10376e 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10376e 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10376e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x103773 [0x48, 0x89, 0x7B, 0x28] (StorePre 0x103773 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x103773 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103773 7 (.base 3 (.d8 0x28)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103773 7 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x103773 0x48 (by decide) 7 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x103777 [0x48, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x103777 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103777 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103777 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103777 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x103777 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10377c [0x4C, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x10377c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10377c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10377c 8 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10377c 8 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10377c 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x103781 [0x4C, 0x89, 0x43, 0x20] (StorePre 0x103781 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x103781 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103781 8 (.base 3 (.d8 0x20)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103781 8 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x103781 0x4c (by decide) 0 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x103785 [0x48, 0x89, 0x7B, 0x18] (StorePre 0x103785 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x103785 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103785 7 (.base 3 (.d8 0x18)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103785 7 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x103785 0x48 (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x103789 [0x89, 0x13] (StorePre 0x103789 2 (fun s => AddrMode.addr (.base 3 .none) s (0x103789 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x103789 2 (.base 3 .none))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x103789 2 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x103789 2 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x10378b [0x89, 0x4B, 0x04] (StorePre 0x10378b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x10378b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x10378b 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10378b 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x10378b 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x10378e [0x48, 0x89, 0x43, 0x08] (StorePre 0x10378e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10378e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10378e 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10378e 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10378e 0x48 (by decide) 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x103792 [0x48, 0x89, 0x73, 0x10] (StorePre 0x103792 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x103792 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103792 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103792 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x103792 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10374f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103752) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103756) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10375b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103760) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103765) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10376a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10376e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 66), (8, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103773) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 66), (8, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103777) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 69), (8, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10377c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 69), (8, 71), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103781) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 69), (8, 71), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103785) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 69), (8, 71), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103789) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 69), (8, 71), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10378b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 69), (8, 71), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10378e) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 69), (8, 71), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103792) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 69), (8, 71), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103796) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 79) (by decide) rfl

theorem block_l10374d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10374d :=
  Rest.liftedBlock (rest_l10374d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10374d x hx)

theorem rest_l103796 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103796 bytes_l103796) (entryMap (live .l103796))
      9 0x103796 bytes_l103796 b_l103796 := by
  have f0 : InstrSpec 0x103796 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x103796) (movR64R64Effect 0x103796 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x103796 0 3).toInstrSpec (mov_r64_r64_effect_step 0x103796 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103799 [0x48, 0x81, 0xC4, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103799) (addR64Imm32Effect 0x103799 4 0x88)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x103799 4 0x88).toInstrSpec (add_r64_imm32_effect_step 0x103799 0x48 0xc4 0x88 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1037a0 [0x5B] (PopPre 0x1037a0) (popR64Effect 0x1037a0 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1037a0 1 3).toInstrSpec (pop_r64_effect_step 0x1037a0 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1037a1 [0x41, 0x5C] (PopPre 0x1037a1) (popR64Effect 0x1037a1 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1037a1 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1037a1 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1037a3 [0x41, 0x5D] (PopPre 0x1037a3) (popR64Effect 0x1037a3 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1037a3 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1037a3 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1037a5 [0x41, 0x5E] (PopPre 0x1037a5) (popR64Effect 0x1037a5 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1037a5 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1037a5 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1037a7 [0x41, 0x5F] (PopPre 0x1037a7) (popR64Effect 0x1037a7 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1037a7 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1037a7 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1037a9 [0x5D] (PopPre 0x1037a9) (popR64Effect 0x1037a9 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1037a9 1 5).toInstrSpec (pop_r64_effect_step 0x1037a9 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x1037aa [0xC3] (RetPre 0x1037aa) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1037aa).toInstrSpec (ret_effect_step 0x1037aa) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103799) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037a0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037a1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037a3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037a5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037a7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037a9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037aa) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l103796 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103796 :=
  Rest.liftedBlock (rest_l103796 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103796 x hx)

theorem rest_l1037ab [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1037ab bytes_l1037ab) (entryMap (live .l1037ab))
      10 0x1037ab bytes_l1037ab b_l1037ab := by
  have f0 : InstrSpec 0x1037ab [0x41, 0x89, 0x6E, 0x18] (StorePre 0x1037ab 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1037ab + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1037ab 5 (.base 14 (.d8 0x18)))
      [.gpr 5, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x1037ab 5 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x1037ab 0x41 (by decide) 5 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1037af [0x48, 0x8D, 0x54, 0x24, 0x78] (fun s => s.RIP = 0x1037af) (leaR64Effect 0x1037af 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1037af 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x1037af 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1037b4 [0x49, 0x8B, 0x45, 0x00] (LoadPre 0x1037b4 (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x1037b4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1037b4 0 (.base 13 (.d8 0x0)))
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1037b4 0 (.base 13 (.d8 0x0))).toInstrSpec (mov_r64_m64_effect_step 0x1037b4 0x49 (by decide) 0 (.base 13 (.d8 0x0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1037b8 [0x49, 0x8B, 0x4D, 0x08] (LoadPre 0x1037b8 (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x1037b8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1037b8 1 (.base 13 (.d8 0x8)))
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1037b8 1 (.base 13 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1037b8 0x49 (by decide) 1 (.base 13 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1037bc [0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x1037bc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1037bc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1037bc 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1037bc 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x1037bc 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1037c4 [0x48, 0x89, 0x44, 0x24, 0x78] (StorePre 0x1037c4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1037c4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1037c4 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1037c4 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x1037c4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1037c9 [0x4C, 0x89, 0x74, 0x24, 0x70] (StorePre 0x1037c9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1037c9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1037c9 14 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1037c9 14 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x1037c9 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1037ce [0x48, 0x8D, 0x7C, 0x24, 0x30] (fun s => s.RIP = 0x1037ce) (leaR64Effect 0x1037ce 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1037ce 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x1037ce 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1037d3 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x1037d3) (movR64R64Effect 0x1037d3 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1037d3 6 14).toInstrSpec (mov_r64_r64_effect_step 0x1037d3 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1037d6 [0xE8, 0x35, 0xCD, 0xFF, 0xFF] (PushPre 0x1037d6 5) (callEffect (fun _ => 0x100510) 0x1037db)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1037d6 0x100510 0x1037db).toInstrSpec (call_rel32_effect_step 0x1037d6 0xffffcd35 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037af) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037b4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037b8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037bc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037c4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037c9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037ce) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037d3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (6, 64), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037d6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 66), (5, 5), (6, 64), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100510) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l1037ab [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1037ab :=
  Rest.liftedBlock (rest_l1037ab code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1037ab x hx)

theorem rest_l1037db [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1037db bytes_l1037db) (entryMap (live .l1037db))
      17 0x1037db bytes_l1037db b_l1037db := by
  have f0 : InstrSpec 0x1037db [0x41, 0x8B, 0x76, 0x18] (LoadPre 0x1037db (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1037db + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1037db 6 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR32M32Effect_footprint 0x1037db 6 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x1037db 0x41 (by decide) 6 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1037df [0x41, 0x8B, 0x4E, 0x1C] (LoadPre 0x1037df (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1037df + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1037df 1 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x1037df 1 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x1037df 0x41 (by decide) 1 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1037e3 [0x29, 0xCE] (fun s => s.RIP = 0x1037e3) (subR32R32Effect 0x1037e3 2 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (subR32R32Effect_footprint 0x1037e3 2 6 1).toInstrSpec (sub_r32_r32_effect_step 0x1037e3 0xce (by decide)) pre_rip
  have f3 : InstrSpec 0x1037e5 [0x0F, 0x96, 0xC0] (fun s => s.RIP = 0x1037e5) (atFlags (condHolds 6) (setccR8Effect 0x1037e5 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x1037e5 3 0 6).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1037e5 6 0xc0 (by decide) (by decide) c)) pre_rip
  have f4 : InstrSpec 0x1037e8 [0x48, 0x8B, 0x54, 0x24, 0x68] (LoadPre 0x1037e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1037e8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1037e8 2 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1037e8 2 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x1037e8 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1037ed [0x49, 0x89, 0x16] (StorePre 0x1037ed 3 (fun s => AddrMode.addr (.base 14 .none) s (0x1037ed + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1037ed 2 (.base 14 .none))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x1037ed 2 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1037ed 0x49 (by decide) 2 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1037f0 [0x4D, 0x89, 0x66, 0x08] (StorePre 0x1037f0 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1037f0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1037f0 12 (.base 14 (.d8 0x8)))
      [.gpr 12, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x1037f0 12 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1037f0 0x4d (by decide) 4 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1037f4 [0x45, 0x89, 0x7E, 0x18] (StorePre 0x1037f4 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1037f4 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1037f4 15 (.base 14 (.d8 0x18)))
      [.gpr 15, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x1037f4 15 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x1037f4 0x45 (by decide) 7 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1037f8 [0x49, 0x8B, 0x56, 0x10] (LoadPre 0x1037f8 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1037f8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1037f8 2 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1037f8 2 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1037f8 0x49 (by decide) 2 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1037fc [0x48, 0x83, 0xFA, 0x01] (fun s => s.RIP = 0x1037fc) (cmpR64Imm8Effect 0x1037fc 2 0x1)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1037fc 2 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x1037fc 0x48 0xfa 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x103800 [0x48, 0x83, 0xD2, 0xFF] (fun s => s.RIP = 0x103800) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x103800 2 0xff))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x103800 2 0xff).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x103800 0x48 0xd2 0xff c (by decide) (by decide) (by decide))) pre_rip
  have f11 : InstrSpec 0x103804 [0x49, 0x89, 0x56, 0x10] (StorePre 0x103804 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x103804 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103804 2 (.base 14 (.d8 0x10)))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x103804 2 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x103804 0x49 (by decide) 2 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x103808 [0x8B, 0x54, 0x24, 0x30] (LoadPre 0x103808 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x103808 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x103808 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x103808 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r32_m32_low_effect_step 0x103808 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10380c [0x83, 0xFA, 0x02] (fun s => s.RIP = 0x10380c) (cmpR32Imm8Effect 0x10380c 3 2 0x2)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x10380c 3 2 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x10380c 0xfa 0x2 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10380f [0x40, 0x0F, 0x95, 0xC7] (fun s => s.RIP = 0x10380f) (atFlags (condHolds 5) (setccR8Effect 0x10380f 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x10380f 4 7 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x10380f 5 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f15 : InstrSpec 0x103813 [0x40, 0x08, 0xC7] (fun s => s.RIP = 0x103813) (orR8R8Effect 0x103813 3 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (orR8R8Effect_footprint 0x103813 3 7 0).toInstrSpec (or_r8_r8_rex_effect_step 0x103813 0x40 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037df) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037e3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 59) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037e5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 55), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037e8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 55), (2, 63), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037ed) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 61), (1, 55), (2, 63), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037f0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 55), (2, 63), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037f4) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 61), (1, 55), (2, 63), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037f8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 61), (1, 55), (2, 68), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037fc) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 61), (1, 55), (2, 68), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103800) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 61), (1, 55), (2, 72), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103804) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 61), (1, 55), (2, 72), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103808) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10380c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10380f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 79), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103813) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 82) f15 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 83) (ρ' := [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103816) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 84) (jcc_rel8_effect_step 0x103816 4 0x6c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1037db [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1037db :=
  Rest.liftedBlock (rest_l1037db code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1037db x hx)

theorem rest_l103818 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103818 bytes_l103818) (entryMap (live .l103818))
      13 0x103818 bytes_l103818 b_l103818 := by
  have f0 : InstrSpec 0x103818 [0x8B, 0x4C, 0x24, 0x34] (LoadPre 0x103818 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x103818 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x103818 1 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x103818 1 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r32_m32_low_effect_step 0x103818 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10381c [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x10381c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10381c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10381c 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10381c 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10381c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103821 [0x48, 0x8B, 0x74, 0x24, 0x40] (LoadPre 0x103821 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x103821 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103821 6 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x103821 6 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x103821 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x103826 [0x48, 0x8B, 0x7C, 0x24, 0x48] (LoadPre 0x103826 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x103826 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103826 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103826 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x103826 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10382b [0x48, 0x89, 0x3C, 0x24] (StorePre 0x10382b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10382b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10382b 7 (.sib 4 none 0 .none))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10382b 7 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10382b 0x48 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10382f [0x48, 0x8B, 0x7C, 0x24, 0x50] (LoadPre 0x10382f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10382f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10382f 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10382f 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x10382f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x103834 [0x48, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x103834 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103834 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103834 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103834 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x103834 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x103839 [0x48, 0x8B, 0x7C, 0x24, 0x58] (LoadPre 0x103839 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x103839 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103839 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103839 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x103839 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10383e [0x48, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x10383e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10383e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10383e 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10383e 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10383e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x103843 [0x48, 0x8B, 0x7C, 0x24, 0x60] (LoadPre 0x103843 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x103843 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103843 7 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103843 7 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x103843 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x103848 [0x48, 0x89, 0x7C, 0x24, 0x18] (StorePre 0x103848 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103848 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103848 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103848 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x103848 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x10384d [0x83, 0xFA, 0x02] (fun s => s.RIP = 0x10384d) (cmpR32Imm8Effect 0x10384d 3 2 0x2)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x10384d 3 2 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x10384d 0xfa 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10381c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103821) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103826) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10382b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10382f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103834) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103839) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10383e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103843) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103848) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10384d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103850) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 73) (jcc_rel32_effect_step 0x103850 5 0xfffffebf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103818 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103818 :=
  Rest.liftedBlock (rest_l103818 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103818 x hx)

theorem rest_l103856 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103856 bytes_l103856) (entryMap (live .l103856))
      10 0x103856 bytes_l103856 b_l103856 := by
  have f0 : InstrSpec 0x103856 [0x48, 0x8B, 0x0C, 0x24] (LoadPre 0x103856 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x103856 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103856 1 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x103856 1 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x103856 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10385a [0x48, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x10385a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10385a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10385a 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10385a 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10385a 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10385f [0x48, 0x89, 0x54, 0x24, 0x28] (StorePre 0x10385f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10385f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10385f 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10385f 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10385f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x103864 [0x48, 0x89, 0x4C, 0x24, 0x20] (StorePre 0x103864 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103864 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103864 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103864 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x103864 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x103869 [0x48, 0x89, 0x53, 0x20] (StorePre 0x103869 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x103869 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103869 2 (.base 3 (.d8 0x20)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103869 2 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x103869 0x48 (by decide) 2 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10386d [0x48, 0x89, 0x4B, 0x18] (StorePre 0x10386d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x10386d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10386d 1 (.base 3 (.d8 0x18)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10386d 1 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10386d 0x48 (by decide) 1 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x103871 [0x48, 0x89, 0x43, 0x08] (StorePre 0x103871 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x103871 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103871 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103871 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x103871 0x48 (by decide) 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x103875 [0x48, 0x89, 0x73, 0x10] (StorePre 0x103875 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x103875 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103875 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103875 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x103875 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x103879 [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x103879 6 (fun s => AddrMode.addr (.base 3 .none) s (0x103879 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x103879 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x103879 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x103879 (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10385a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10385f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103864) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103869) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10386d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103871) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103875) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103879) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10387f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 64) (jmp_rel32_effect_step 0x10387f 0xffffff12 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103856 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103856 :=
  Rest.liftedBlock (rest_l103856 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103856 x hx)

theorem rest_l103884 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103884 bytes_l103884) (entryMap (live .l103884))
      7 0x103884 bytes_l103884 b_l103884 := by
  have f0 : InstrSpec 0x103884 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x103884 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x103884 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x103884 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x103884 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x103884 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x103889 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x103889) (movR64R64Effect 0x103889 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x103889 0 1).toInstrSpec (mov_r64_r64_effect_step 0x103889 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10388c [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x10388c) (shlR64Effect 0x10388c 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10388c 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x10388c 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103890 [0x48, 0x83, 0xC8, 0x13] (fun s => s.RIP = 0x103890) (orR64Imm8Effect 0x103890 0 0x13)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x103890 0 0x13).toInstrSpec (or_r64_imm8_effect_step 0x103890 0x48 0xc8 0x13 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103894 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103894) (movR32Imm32Effect 0x103894 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x103894 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x103894 0xba (by decide) 0x1) pre_rip
  have f5 : InstrSpec 0x103899 [0x31, 0xFF] (fun s => s.RIP = 0x103899) (xorR32R32Effect 0x103899 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103899 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x103899 0xff (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103889) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10388c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103890) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103894) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 58), (1, 1), (2, 60), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103899) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 58), (1, 1), (2, 60), (3, 3), (4, 4), (6, 6), (7, 62), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10389b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 64) (jmp_rel32_effect_step 0x10389b 0xfffffead (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103884 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103884 :=
  Rest.liftedBlock (rest_l103884 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103884 x hx)

theorem rest_l1038a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1038a0 bytes_l1038a0) (entryMap (live .l1038a0))
      4 0x1038a0 bytes_l1038a0 b_l1038a0 := by
  have f0 : InstrSpec 0x1038a0 [0x31, 0xD2] (fun s => s.RIP = 0x1038a0) (xorR32R32Effect 0x1038a0 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1038a0 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x1038a0 0xd2 (by decide)) pre_rip
  have f1 : InstrSpec 0x1038a2 [0xB8, 0x0C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1038a2) (movR32Imm32Effect 0x1038a2 5 0 0xc)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1038a2 5 0 0xc).toInstrSpec (mov_r32_imm32_effect_step 0x1038a2 0xb8 (by decide) 0xc) pre_rip
  have f2 : InstrSpec 0x1038a7 [0x31, 0xFF] (fun s => s.RIP = 0x1038a7) (xorR32R32Effect 0x1038a7 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1038a7 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x1038a7 0xff (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038a2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038a7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038a9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x1038a9 0xfffffe9f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1038a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1038a0 :=
  Rest.liftedBlock (rest_l1038a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1038a0 x hx)

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

theorem_by block_l103670_eval :
    program.runBlock (dialect code) ⟨.l103670, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103694_eval :
    program.runBlock (dialect code) ⟨.l103694, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1036b5_eval :
    program.runBlock (dialect code) ⟨.l1036b5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1036be_eval :
    program.runBlock (dialect code) ⟨.l1036be, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1036d9_eval :
    program.runBlock (dialect code) ⟨.l1036d9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1036e0_eval :
    program.runBlock (dialect code) ⟨.l1036e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103715_eval :
    program.runBlock (dialect code) ⟨.l103715, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103724_eval :
    program.runBlock (dialect code) ⟨.l103724, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103734_eval :
    program.runBlock (dialect code) ⟨.l103734, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103740_eval :
    program.runBlock (dialect code) ⟨.l103740, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10374d_eval :
    program.runBlock (dialect code) ⟨.l10374d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103796_eval :
    program.runBlock (dialect code) ⟨.l103796, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1037ab_eval :
    program.runBlock (dialect code) ⟨.l1037ab, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1037db_eval :
    program.runBlock (dialect code) ⟨.l1037db, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103818_eval :
    program.runBlock (dialect code) ⟨.l103818, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103856_eval :
    program.runBlock (dialect code) ⟨.l103856, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103884_eval :
    program.runBlock (dialect code) ⟨.l103884, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1038a0_eval :
    program.runBlock (dialect code) ⟨.l1038a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
