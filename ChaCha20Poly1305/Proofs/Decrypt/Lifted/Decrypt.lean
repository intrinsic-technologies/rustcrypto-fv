import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Program
import X86Proofs.Instructions.Branch.Triple
import ChaCha20Poly1305.Proofs.Common.Lift.Generated.Values

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

theorem rest_l1014c0_1 [Bindings] (code : CodeMap) :
    Rest (n := 90) code lifted (codeRange 0x1014c0 bytes_l1014c0) [(0, 86), (1, 88), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x101513 bytes_l1014c0_1 b_l1014c0_1 := by
  have f20 : InstrSpec 0x101513 [0x48, 0x89, 0x4C, 0x24, 0x40] (StorePre 0x101513 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x101513 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101513 1 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101513 1 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x101513 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x101518 [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x101518 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x101518 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101518 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101518 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x101518 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x10151d [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x10151d) (testR64R64Effect 0x10151d 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x10151d 14 14).toInstrSpec (test_r64_r64_effect_step 0x10151d 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 86), (1, 88), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101518) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 86), (1, 88), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10151d) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f22 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 93) f22 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 94) (ρ' := [(0, 86), (1, 88), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (19, 92), (20, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101520) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 95) (jcc_rel32_effect_step 0x101520 8 0x113) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l1014c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1014c0 bytes_l1014c0) (entryMap (live .l1014c0))
      24 0x1014c0 bytes_l1014c0 b_l1014c0 := by
  have f0 : InstrSpec 0x1014c0 [0x55] (PushPre 0x1014c0 1) (pushR64Effect 0x1014c0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1014c0 1 5).toInstrSpec (push_r64_effect_step 0x1014c0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1014c1 [0x41, 0x57] (PushPre 0x1014c1 2) (pushR64Effect 0x1014c1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1014c1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1014c1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1014c3 [0x41, 0x56] (PushPre 0x1014c3 2) (pushR64Effect 0x1014c3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1014c3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1014c3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1014c5 [0x41, 0x55] (PushPre 0x1014c5 2) (pushR64Effect 0x1014c5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1014c5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1014c5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1014c7 [0x41, 0x54] (PushPre 0x1014c7 2) (pushR64Effect 0x1014c7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1014c7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1014c7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1014c9 [0x53] (PushPre 0x1014c9 1) (pushR64Effect 0x1014c9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1014c9 1 3).toInstrSpec (push_r64_effect_step 0x1014c9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1014ca [0x48, 0x83, 0xEC, 0x58] (fun s => s.RIP = 0x1014ca) (subR64Imm8Effect 0x1014ca 4 0x58)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1014ca 4 0x58).toInstrSpec (sub_r64_imm8_effect_step 0x1014ca 0x48 0xec 0x58 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1014ce [0x49, 0x89, 0xCD] (fun s => s.RIP = 0x1014ce) (movR64R64Effect 0x1014ce 13 1)
      [.gpr 1] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1014ce 13 1).toInstrSpec (mov_r64_r64_effect_step 0x1014ce 0x49 0xcd (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1014d1 [0x4C, 0x8B, 0xB4, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x1014d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1014d1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1014d1 14 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x1014d1 14 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x1014d1 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1014d9 [0x4C, 0x89, 0x05, 0x20, 0xEB, 0x1F, 0x00] (StorePre 0x1014d9 7 (fun s => AddrMode.addr (.rip 0x1feb20) s (0x1014d9 + BitVec.ofNat 64 7)) 8) (movM64R64Effect 0x1014d9 8 (.rip 0x1feb20))
      [.gpr 8] [] [.rip] :=
    (movM64R64Effect_footprint 0x1014d9 8 (.rip 0x1feb20)).toInstrSpec (mov_m64_r64_effect_step 0x1014d9 0x4c (by decide) 0 (.rip 0x1feb20) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1014e0 [0x4C, 0x03, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x1014e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1014e0 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x1014e0 8 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 8, .gpr 4] [] [.reg 8, .flags, .rip] :=
    (addR64M64Effect_footprint 0x1014e0 8 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (add_r64_m64_effect_step 0x1014e0 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1014e8 [0x48, 0xC7, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x1014e8) (movR64Imm32Effect 0x1014e8 0 0xffffffff)
      [] [] [.reg 0, .rip] :=
    (movR64Imm32Effect_footprint 0x1014e8 0 0xffffffff).toInstrSpec (mov_r64_imm32_effect_step 0x1014e8 0x48 0xc0 (by decide) (by decide) (by decide) 0xffffffff) pre_rip
  have f12 : InstrSpec 0x1014ef [0x49, 0x0F, 0x43, 0xC0] (fun s => s.RIP = 0x1014ef) (atFlags (condHolds 3) (cmovR64R64Effect 0x1014ef 4 0 8))
      [.gpr 0, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .rip] :=
    (cmovR64R64Effect_footprint 0x1014ef 4 0 8 3).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x1014ef 3 0x49 (by decide) 0xc0 (by decide) c)) pre_rip
  have f13 : InstrSpec 0x1014f3 [0x48, 0x89, 0x05, 0x0E, 0xEB, 0x1F, 0x00] (StorePre 0x1014f3 7 (fun s => AddrMode.addr (.rip 0x1feb0e) s (0x1014f3 + BitVec.ofNat 64 7)) 8) (movM64R64Effect 0x1014f3 0 (.rip 0x1feb0e))
      [.gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x1014f3 0 (.rip 0x1feb0e)).toInstrSpec (mov_m64_r64_effect_step 0x1014f3 0x48 (by decide) 0 (.rip 0x1feb0e) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1014fa [0x48, 0x8B, 0x47, 0x18] (LoadPre 0x1014fa (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x1014fa + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1014fa 0 (.base 7 (.d8 0x18)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1014fa 0 (.base 7 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1014fa 0x48 (by decide) 0 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1014fe [0x48, 0x89, 0x44, 0x24, 0x50] (StorePre 0x1014fe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1014fe + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1014fe 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1014fe 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x1014fe 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x101503 [0x48, 0x8B, 0x47, 0x10] (LoadPre 0x101503 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x101503 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101503 0 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101503 0 (.base 7 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x101503 0x48 (by decide) 0 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x101507 [0x48, 0x89, 0x44, 0x24, 0x48] (StorePre 0x101507 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101507 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101507 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101507 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x101507 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x10150c [0x48, 0x8B, 0x07] (LoadPre 0x10150c (fun s => AddrMode.addr (.base 7 .none) s (0x10150c + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10150c 0 (.base 7 .none))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10150c 0 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10150c 0x48 (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x10150f [0x48, 0x8B, 0x4F, 0x08] (LoadPre 0x10150f (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10150f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10150f 1 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10150f 1 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10150f 0x48 (by decide) 1 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014c3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014c5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014c7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014c9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014ca) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014ce) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 67), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014d1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014d9) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014e0) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014e8) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014ef) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014f3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014fa) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014fe) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101503) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101507) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 83), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10150c) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 86), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10150f) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 86), (1, 88), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (16, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101513) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1014c0_1 code

theorem block_l1014c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1014c0 :=
  Rest.liftedBlock (rest_l1014c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1014c0 x hx)

theorem rest_l101526 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101526 bytes_l101526) (entryMap (live .l101526))
      1 0x101526 bytes_l101526 b_l101526 := by
  exact Rest.jcc (n := 53) (jcc_rel32_effect_step 0x101526 4 0xe5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101526 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101526 :=
  Rest.liftedBlock (rest_l101526 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101526 x hx)

theorem rest_l10152c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10152c bytes_l10152c) (entryMap (live .l10152c))
      4 0x10152c bytes_l10152c b_l10152c := by
  have f0 : InstrSpec 0x10152c [0x4C, 0x89, 0xCB] (fun s => s.RIP = 0x10152c) (movR64R64Effect 0x10152c 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10152c 3 9).toInstrSpec (mov_r64_r64_effect_step 0x10152c 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10152f [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x10152f) (movR64R64Effect 0x10152f 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10152f 15 2).toInstrSpec (mov_r64_r64_effect_step 0x10152f 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101532 [0x49, 0x89, 0xF4] (fun s => s.RIP = 0x101532) (movR64R64Effect 0x101532 12 6)
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x101532 12 6).toInstrSpec (mov_r64_r64_effect_step 0x101532 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101535 [0xE8, 0x66, 0x05, 0x00, 0x00] (PushPre 0x101535 5) (callEffect (fun _ => 0x101aa0) 0x10153a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101535 0x101aa0 0x10153a).toInstrSpec (call_rel32_effect_step 0x101535 0x566 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10152f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101532) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 57), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101535) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 59), (5, 5), (6, 6), (7, 7), (9, 9), (12, 57), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101aa0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10152c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10152c :=
  Rest.liftedBlock (rest_l10152c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10152c x hx)

theorem rest_l10153a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10153a bytes_l10153a) (entryMap (live .l10153a))
      5 0x10153a bytes_l10153a b_l10153a := by
  have f0 : InstrSpec 0x10153a [0x48, 0x8B, 0x2D, 0xBF, 0xEA, 0x1F, 0x00] (LoadPre 0x10153a (fun s => AddrMode.addr (.rip 0x1feabf) s (0x10153a + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x10153a 5 (.rip 0x1feabf))
      [] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x10153a 5 (.rip 0x1feabf)).toInstrSpec (mov_r64_m64_effect_step 0x10153a 0x48 (by decide) 5 (.rip 0x1feabf) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101541 [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x101541) (movR64R64Effect 0x101541 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101541 0 5).toInstrSpec (mov_r64_r64_effect_step 0x101541 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101544 [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101544) (movR32Imm32Effect 0x101544 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x101544 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x101544 0xbf (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x101549 [0x4C, 0x01, 0xF0] (fun s => s.RIP = 0x101549) (addR64R64Effect 0x101549 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101549 0 14).toInstrSpec (add_r64_r64_effect_step 0x101549 0x4c 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101541) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101544) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101549) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10154c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel32_effect_step 0x10154c 2 0xe9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10153a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10153a :=
  Rest.liftedBlock (rest_l10153a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10153a x hx)

theorem rest_l101552 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101552 bytes_l101552) (entryMap (live .l101552))
      3 0x101552 bytes_l101552 b_l101552 := by
  have f0 : InstrSpec 0x101552 [0x48, 0x8B, 0x0D, 0xAF, 0xEA, 0x1F, 0x00] (LoadPre 0x101552 (fun s => AddrMode.addr (.rip 0x1feaaf) s (0x101552 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x101552 1 (.rip 0x1feaaf))
      [] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101552 1 (.rip 0x1feaaf)).toInstrSpec (mov_r64_m64_effect_step 0x101552 0x48 (by decide) 1 (.rip 0x1feaaf) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101559 [0x48, 0x39, 0xC8] (fun s => s.RIP = 0x101559) (cmpR64R64Effect 0x101559 0 1)
      [.gpr 0, .gpr 1] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x101559 0 1).toInstrSpec (cmp_r64_r64_effect_step 0x101559 0x48 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101559) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10155c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel32_effect_step 0x10155c 7 0xd9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101552 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101552 :=
  Rest.liftedBlock (rest_l101552 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101552 x hx)

theorem rest_l101562 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101562 bytes_l101562) (entryMap (live .l101562))
      3 0x101562 bytes_l101562 b_l101562 := by
  have f0 : InstrSpec 0x101562 [0x48, 0x89, 0x05, 0x97, 0xEA, 0x1F, 0x00] (StorePre 0x101562 7 (fun s => AddrMode.addr (.rip 0x1fea97) s (0x101562 + BitVec.ofNat 64 7)) 8) (movM64R64Effect 0x101562 0 (.rip 0x1fea97))
      [.gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x101562 0 (.rip 0x1fea97)).toInstrSpec (mov_m64_r64_effect_step 0x101562 0x48 (by decide) 0 (.rip 0x1fea97) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x101569 [0x48, 0x85, 0xED] (fun s => s.RIP = 0x101569) (testR64R64Effect 0x101569 5 5)
      [.gpr 5, .gpr 5] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x101569 5 5).toInstrSpec (test_r64_r64_effect_step 0x101569 0x48 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101569) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10156c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x10156c 4 0xc9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101562 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101562 :=
  Rest.liftedBlock (rest_l101562 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101562 x hx)

theorem rest_l101572 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101572 bytes_l101572) (entryMap (live .l101572))
      6 0x101572 bytes_l101572 b_l101572 := by
  have f0 : InstrSpec 0x101572 [0x4C, 0x89, 0x74, 0x24, 0x08] (StorePre 0x101572 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101572 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101572 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101572 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x101572 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x101577 [0x48, 0x89, 0x6C, 0x24, 0x10] (StorePre 0x101577 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101577 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101577 5 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101577 5 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x101577 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10157c [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x10157c) (movR64R64Effect 0x10157c 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10157c 7 5).toInstrSpec (mov_r64_r64_effect_step 0x10157c 0x48 0xef (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10157f [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x10157f) (movR64R64Effect 0x10157f 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10157f 6 13).toInstrSpec (mov_r64_r64_effect_step 0x10157f 0x4c 0xee (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101582 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x101582) (movR64R64Effect 0x101582 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x101582 2 14).toInstrSpec (mov_r64_r64_effect_step 0x101582 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101585 [0xFF, 0x15, 0x1D, 0xFE, 0x0F, 0x00] (GoesTo (CallMemPre 0x101585 (.rip 0xffe1d)) (callEffect (callMemPtr 0x101585 (.rip 0xffe1d)) (0x101585 + BitVec.ofNat 64 (callMemLen (.rip 0xffe1d)))) 0x102dc0) (callEffect (callMemPtr 0x101585 (.rip 0xffe1d)) (0x101585 + BitVec.ofNat 64 (callMemLen (.rip 0xffe1d))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x101585 (.rip 0xffe1d)).toInstrSpec (call_m64_effect_step 0x101585 (.rip 0xffe1d) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x102dc0
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101577) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10157c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10157f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101582) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101585) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dc0) f5 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l101572 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101572 :=
  Rest.liftedBlock (rest_l101572 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101572 x hx)

theorem rest_l10158b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10158b bytes_l10158b) (entryMap (live .l10158b))
      3 0x10158b bytes_l10158b b_l10158b := by
  have f0 : InstrSpec 0x10158b [0x4C, 0x89, 0x74, 0x24, 0x18] (StorePre 0x10158b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10158b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10158b 14 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10158b 14 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10158b 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x101590 [0x49, 0x83, 0xFE, 0x10] (fun s => s.RIP = 0x101590) (cmpR64Imm8Effect 0x101590 14 0x10)
      [.gpr 14] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x101590 14 0x10).toInstrSpec (cmp_r64_imm8_effect_step 0x101590 0x49 0xfe 0x10 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101590) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (14, 14), (15, 15), (16, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101594) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x101594 2 0x7b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10158b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10158b :=
  Rest.liftedBlock (rest_l10158b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10158b x hx)

theorem rest_l101596 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101596 bytes_l101596) (entryMap (live .l101596))
      13 0x101596 bytes_l101596 b_l101596 := by
  have f0 : InstrSpec 0x101596 [0x48, 0x8B, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x101596 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x101596 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101596 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101596 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x101596 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10159e [0x4D, 0x8D, 0x6E, 0xF0] (fun s => s.RIP = 0x10159e) (leaR64Effect 0x10159e 13 (.base 14 (.d8 0xf0)))
      [.gpr 14] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x10159e 13 (.base 14 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x10159e 0x4d (by decide) 5 (.base 14 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1015a2 [0x4E, 0x8B, 0x4C, 0x35, 0xF0] (LoadPre 0x1015a2 (fun s => AddrMode.addr (.sib 5 (some 14) 0 (.d8 0xf0)) s (0x1015a2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1015a2 9 (.sib 5 (some 14) 0 (.d8 0xf0)))
      [.gpr 5, .gpr 14] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1015a2 9 (.sib 5 (some 14) 0 (.d8 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x1015a2 0x4e (by decide) 1 (.sib 5 (some 14) 0 (.d8 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1015a7 [0x4A, 0x8B, 0x44, 0x35, 0xF8] (LoadPre 0x1015a7 (fun s => AddrMode.addr (.sib 5 (some 14) 0 (.d8 0xf8)) s (0x1015a7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1015a7 0 (.sib 5 (some 14) 0 (.d8 0xf8)))
      [.gpr 5, .gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1015a7 0 (.sib 5 (some 14) 0 (.d8 0xf8))).toInstrSpec (mov_r64_m64_effect_step 0x1015a7 0x4a (by decide) 0 (.sib 5 (some 14) 0 (.d8 0xf8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1015ac [0x48, 0x89, 0x6C, 0x24, 0x20] (StorePre 0x1015ac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1015ac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1015ac 5 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1015ac 5 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1015ac 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1015b1 [0x48, 0x89, 0x6C, 0x24, 0x28] (StorePre 0x1015b1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1015b1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1015b1 5 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1015b1 5 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1015b1 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1015b6 [0x4C, 0x89, 0x6C, 0x24, 0x30] (StorePre 0x1015b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1015b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1015b6 13 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1015b6 13 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1015b6 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1015bb [0x48, 0x89, 0x04, 0x24] (StorePre 0x1015bb 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1015bb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1015bb 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1015bb 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1015bb 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1015bf [0x48, 0x8D, 0x7C, 0x24, 0x38] (fun s => s.RIP = 0x1015bf) (leaR64Effect 0x1015bf 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1015bf 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x1015bf 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1015c4 [0x4C, 0x8D, 0x44, 0x24, 0x20] (fun s => s.RIP = 0x1015c4) (leaR64Effect 0x1015c4 8 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x1015c4 8 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x1015c4 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1015c9 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x1015c9) (movR64R64Effect 0x1015c9 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1015c9 6 12).toInstrSpec (mov_r64_r64_effect_step 0x1015c9 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1015cc [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x1015cc) (movR64R64Effect 0x1015cc 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1015cc 2 15).toInstrSpec (mov_r64_r64_effect_step 0x1015cc 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1015cf [0xE8, 0x1C, 0xEC, 0xFF, 0xFF] (PushPre 0x1015cf 5) (callEffect (fun _ => 0x1001f0) 0x1015d4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1015cf 0x1001f0 0x1015d4).toInstrSpec (call_rel32_effect_step 0x1015cf 0xffffec1c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10159e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015a2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (9, 57), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015a7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 53), (3, 3), (4, 4), (5, 5), (9, 57), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015ac) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 53), (3, 3), (4, 4), (5, 5), (9, 57), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015b1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 53), (3, 3), (4, 4), (5, 5), (9, 57), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015b6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 53), (3, 3), (4, 4), (5, 5), (9, 57), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015bb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 53), (3, 3), (4, 4), (5, 5), (9, 57), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015bf) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 53), (3, 3), (4, 4), (5, 5), (7, 65), (9, 57), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015c4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 53), (3, 3), (4, 4), (5, 5), (7, 65), (8, 67), (9, 57), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015c9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 53), (3, 3), (4, 4), (5, 5), (6, 69), (7, 65), (8, 67), (9, 57), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015cc) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 53), (2, 71), (3, 3), (4, 4), (5, 5), (6, 69), (7, 65), (8, 67), (9, 57), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015cf) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 59), (1, 53), (2, 71), (3, 3), (4, 73), (5, 5), (6, 69), (7, 65), (8, 67), (9, 57), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001f0) f12 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l101596 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101596 :=
  Rest.liftedBlock (rest_l101596 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101596 x hx)

theorem rest_l1015d4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1015d4 bytes_l1015d4) (entryMap (live .l1015d4))
      2 0x1015d4 bytes_l1015d4 b_l1015d4 := by
  have f0 : InstrSpec 0x1015d4 [0x84, 0xC0] (fun s => s.RIP = 0x1015d4) (testR8R8Effect 0x1015d4 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1015d4 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x1015d4 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015d6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1015d6 5 0x39) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1015d4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1015d4 :=
  Rest.liftedBlock (rest_l1015d4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1015d4 x hx)

theorem rest_l1015d8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1015d8 bytes_l1015d8) (entryMap (live .l1015d8))
      3 0x1015d8 bytes_l1015d8 b_l1015d8 := by
  have f0 : InstrSpec 0x1015d8 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x1015d8) (leaR64Effect 0x1015d8 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1015d8 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x1015d8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1015dd [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x1015dd) (movR64R64Effect 0x1015dd 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1015dd 6 13).toInstrSpec (mov_r64_r64_effect_step 0x1015dd 0x4c 0xee (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1015e0 [0xE8, 0x3B, 0x0A, 0x00, 0x00] (PushPre 0x1015e0 5) (callEffect (fun _ => 0x102020) 0x1015e5)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1015e0 0x102020 0x1015e5).toInstrSpec (call_rel32_effect_step 0x1015e0 0xa3b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015dd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015e0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102020) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l1015d8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1015d8 :=
  Rest.liftedBlock (rest_l1015d8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1015d8 x hx)

theorem rest_l1015e5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1015e5 bytes_l1015e5) (entryMap (live .l1015e5))
      2 0x1015e5 bytes_l1015e5 b_l1015e5 := by
  have f0 : InstrSpec 0x1015e5 [0x48, 0x83, 0x7C, 0x24, 0x08, 0xFF] (LoadPre 0x1015e5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1015e5 + BitVec.ofNat 64 6)) 8) (cmpMImm8Effect 0x1015e5 6 64 (.sib 4 none 0 (.d8 0x8)) 0xff)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect64_footprint 0x1015e5 6 (.sib 4 none 0 (.d8 0x8)) 0xff).toInstrSpec (cmp_m64_imm8_effect_step 0x1015e5 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0xff) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015eb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1015eb 4 0x24) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1015e5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1015e5 :=
  Rest.liftedBlock (rest_l1015e5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1015e5 x hx)

theorem rest_l1015ed [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1015ed bytes_l1015ed) (entryMap (live .l1015ed))
      4 0x1015ed bytes_l1015ed b_l1015ed := by
  have f0 : InstrSpec 0x1015ed [0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x1015ed (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1015ed + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1015ed 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1015ed 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x1015ed 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1015f5 [0x48, 0x8B, 0x54, 0x24, 0x18] (LoadPre 0x1015f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1015f5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1015f5 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1015f5 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1015f5 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1015fa [0x48, 0x39, 0xC2] (fun s => s.RIP = 0x1015fa) (cmpR64R64Effect 0x1015fa 2 0)
      [.gpr 2, .gpr 0] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1015fa 2 0).toInstrSpec (cmp_r64_r64_effect_step 0x1015fa 0x48 0xc2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015f5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015fa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015fd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x1015fd 7 0x26) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1015ed [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1015ed :=
  Rest.liftedBlock (rest_l1015ed code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1015ed x hx)

theorem rest_l1015ff [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1015ff bytes_l1015ff) (entryMap (live .l1015ff))
      3 0x1015ff bytes_l1015ff b_l1015ff := by
  have f0 : InstrSpec 0x1015ff [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x1015ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1015ff + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1015ff 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1015ff 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1015ff 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101604 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x101604) (movR64R64Effect 0x101604 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101604 7 3).toInstrSpec (mov_r64_r64_effect_step 0x101604 0x48 0xdf (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101607 [0xFF, 0x15, 0x9B, 0xFD, 0x0F, 0x00] (GoesTo (CallMemPre 0x101607 (.rip 0xffd9b)) (callEffect (callMemPtr 0x101607 (.rip 0xffd9b)) (0x101607 + BitVec.ofNat 64 (callMemLen (.rip 0xffd9b)))) 0x102dc0) (callEffect (callMemPtr 0x101607 (.rip 0xffd9b)) (0x101607 + BitVec.ofNat 64 (callMemLen (.rip 0xffd9b))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x101607 (.rip 0xffd9b)).toInstrSpec (call_m64_effect_step 0x101607 (.rip 0xffd9b) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x102dc0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101604) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101607) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 53), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dc0) f2 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l1015ff [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1015ff :=
  Rest.liftedBlock (rest_l1015ff code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1015ff x hx)

theorem rest_l10160d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10160d bytes_l10160d) (entryMap (live .l10160d))
      2 0x10160d bytes_l10160d b_l10160d := by
  have f0 : InstrSpec 0x10160d [0x31, 0xC0] (fun s => s.RIP = 0x10160d) (xorR32R32Effect 0x10160d 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10160d 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x10160d 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10160f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x10160f 0x5 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10160d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10160d :=
  Rest.liftedBlock (rest_l10160d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10160d x hx)

theorem rest_l101611 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101611 bytes_l101611) (entryMap (live .l101611))
      1 0x101611 bytes_l101611 b_l101611 := by
  have f0 : InstrSpec 0x101611 [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101611) (movR32Imm32Effect 0x101611 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x101611 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x101611 0xb8 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101616) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l101611 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101611 :=
  Rest.liftedBlock (rest_l101611 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101611 x hx)

theorem rest_l101616 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101616 bytes_l101616) (entryMap (live .l101616))
      8 0x101616 bytes_l101616 b_l101616 := by
  have f0 : InstrSpec 0x101616 [0x48, 0x83, 0xC4, 0x58] (fun s => s.RIP = 0x101616) (addR64Imm8Effect 0x101616 4 0x58)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x101616 4 0x58).toInstrSpec (add_r64_imm8_effect_step 0x101616 0x48 0xc4 0x58 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10161a [0x5B] (PopPre 0x10161a) (popR64Effect 0x10161a 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10161a 1 3).toInstrSpec (pop_r64_effect_step 0x10161a 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x10161b [0x41, 0x5C] (PopPre 0x10161b) (popR64Effect 0x10161b 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10161b 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10161b 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10161d [0x41, 0x5D] (PopPre 0x10161d) (popR64Effect 0x10161d 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10161d 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10161d 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10161f [0x41, 0x5E] (PopPre 0x10161f) (popR64Effect 0x10161f 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10161f 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10161f 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101621 [0x41, 0x5F] (PopPre 0x101621) (popR64Effect 0x101621 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101621 2 15).toInstrSpec (pop_r64_rex_effect_step 0x101621 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x101623 [0x5D] (PopPre 0x101623) (popR64Effect 0x101623 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101623 1 5).toInstrSpec (pop_r64_effect_step 0x101623 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x101624 [0xC3] (RetPre 0x101624) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x101624).toInstrSpec (ret_effect_step 0x101624) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10161a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10161b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (9, 9), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10161d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10161f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101621) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101623) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101624) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l101616 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101616 :=
  Rest.liftedBlock (rest_l101616 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101616 x hx)

theorem rest_l101625 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101625 bytes_l101625) (entryMap (live .l101625))
      0 0x101625 bytes_l101625 b_l101625 := by
  exact Rest.cut

theorem block_l101625 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101625 :=
  Rest.liftedBlock (rest_l101625 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101625 x hx)

theorem rest_l101639 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101639 bytes_l101639) (entryMap (live .l101639))
      0 0x101639 bytes_l101639 b_l101639 := by
  exact Rest.cut

theorem block_l101639 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101639 :=
  Rest.liftedBlock (rest_l101639 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101639 x hx)

theorem rest_l10163b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10163b bytes_l10163b) (entryMap (live .l10163b))
      0 0x10163b bytes_l10163b b_l10163b := by
  exact Rest.cut

theorem block_l10163b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10163b :=
  Rest.liftedBlock (rest_l10163b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10163b x hx)

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

theorem_by block_l1014c0_eval :
    program.runBlock (dialect code) ⟨.l1014c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101526_eval :
    program.runBlock (dialect code) ⟨.l101526, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10152c_eval :
    program.runBlock (dialect code) ⟨.l10152c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10153a_eval :
    program.runBlock (dialect code) ⟨.l10153a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101552_eval :
    program.runBlock (dialect code) ⟨.l101552, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101562_eval :
    program.runBlock (dialect code) ⟨.l101562, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101572_eval :
    program.runBlock (dialect code) ⟨.l101572, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10158b_eval :
    program.runBlock (dialect code) ⟨.l10158b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101596_eval :
    program.runBlock (dialect code) ⟨.l101596, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1015d4_eval :
    program.runBlock (dialect code) ⟨.l1015d4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1015d8_eval :
    program.runBlock (dialect code) ⟨.l1015d8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1015e5_eval :
    program.runBlock (dialect code) ⟨.l1015e5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1015ed_eval :
    program.runBlock (dialect code) ⟨.l1015ed, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1015ff_eval :
    program.runBlock (dialect code) ⟨.l1015ff, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10160d_eval :
    program.runBlock (dialect code) ⟨.l10160d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101611_eval :
    program.runBlock (dialect code) ⟨.l101611, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101616_eval :
    program.runBlock (dialect code) ⟨.l101616, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101625_eval :
    program.runBlock (dialect code) ⟨.l101625, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101639_eval :
    program.runBlock (dialect code) ⟨.l101639, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10163b_eval :
    program.runBlock (dialect code) ⟨.l10163b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
