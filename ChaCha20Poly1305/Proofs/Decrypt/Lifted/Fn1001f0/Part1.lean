import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Program
import X86Proofs.Instructions.Branch.Triple
import ChaCha20Poly1305.Proofs.Common.Lift.Generated.Values

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Decrypt.Movsd

theorem rest_l1001f0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1001f0 bytes_l1001f0) (entryMap (live .l1001f0))
      20 0x1001f0 bytes_l1001f0 b_l1001f0 := by
  have f0 : InstrSpec 0x1001f0 [0x55] (PushPre 0x1001f0 1) (pushR64Effect 0x1001f0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1001f0 1 5).toInstrSpec (push_r64_effect_step 0x1001f0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1001f1 [0x41, 0x57] (PushPre 0x1001f1 2) (pushR64Effect 0x1001f1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1001f1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1001f1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1001f3 [0x41, 0x56] (PushPre 0x1001f3 2) (pushR64Effect 0x1001f3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1001f3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1001f3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1001f5 [0x41, 0x55] (PushPre 0x1001f5 2) (pushR64Effect 0x1001f5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1001f5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1001f5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1001f7 [0x41, 0x54] (PushPre 0x1001f7 2) (pushR64Effect 0x1001f7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1001f7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1001f7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1001f9 [0x53] (PushPre 0x1001f9 1) (pushR64Effect 0x1001f9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1001f9 1 3).toInstrSpec (push_r64_effect_step 0x1001f9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1001fa [0x48, 0x81, 0xEC, 0x88, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1001fa) (subR64Imm32Effect 0x1001fa 4 0x188)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x1001fa 4 0x188).toInstrSpec (sub_r64_imm32_effect_step 0x1001fa 0x48 0xec 0x188 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100201 [0x4D, 0x89, 0xCE] (fun s => s.RIP = 0x100201) (movR64R64Effect 0x100201 14 9)
      [.gpr 9] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x100201 14 9).toInstrSpec (mov_r64_r64_effect_step 0x100201 0x4d 0xce (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100204 [0x4C, 0x89, 0xC3] (fun s => s.RIP = 0x100204) (movR64R64Effect 0x100204 3 8)
      [.gpr 8] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x100204 3 8).toInstrSpec (mov_r64_r64_effect_step 0x100204 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x100207 [0x48, 0x89, 0xCD] (fun s => s.RIP = 0x100207) (movR64R64Effect 0x100207 5 1)
      [.gpr 1] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x100207 5 1).toInstrSpec (mov_r64_r64_effect_step 0x100207 0x48 0xcd (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10020a [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x10020a) (movR64R64Effect 0x10020a 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10020a 13 2).toInstrSpec (mov_r64_r64_effect_step 0x10020a 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10020d [0x48, 0xB8, 0x32, 0x2D, 0x62, 0x79, 0x74, 0x65, 0x20, 0x6B] (fun s => s.RIP = 0x10020d) (movR64Imm64Effect 0x10020d 0 0x6b20657479622d32)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x10020d 0 0x6b20657479622d32).toInstrSpec (mov_r64_imm64_effect_step 0x10020d 0x48 0xb8 (by decide) (by decide) 0x6b20657479622d32) pre_rip
  have f12 : InstrSpec 0x100217 [0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x100217 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x100217 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100217 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100217 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x100217 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x10021f [0x48, 0xB8, 0x65, 0x78, 0x70, 0x61, 0x6E, 0x64, 0x20, 0x33] (fun s => s.RIP = 0x10021f) (movR64Imm64Effect 0x10021f 0 0x3320646e61707865)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x10021f 0 0x3320646e61707865).toInstrSpec (mov_r64_imm64_effect_step 0x10021f 0x48 0xb8 (by decide) (by decide) 0x3320646e61707865) pre_rip
  have f14 : InstrSpec 0x100229 [0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x100229 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x100229 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100229 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100229 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x100229 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x100231 [0x48, 0x8B, 0x07] (LoadPre 0x100231 (fun s => AddrMode.addr (.base 7 .none) s (0x100231 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100231 0 (.base 7 .none))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100231 0 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x100231 0x48 (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x100234 [0x48, 0x8B, 0x4F, 0x08] (LoadPre 0x100234 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x100234 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100234 1 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100234 1 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x100234 0x48 (by decide) 1 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x100238 [0x48, 0x89, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x100238 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x100238 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100238 0 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100238 0 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x100238 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x100240 [0x48, 0x89, 0x8C, 0x24, 0xE8, 0x00, 0x00, 0x00] (StorePre 0x100240 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x100240 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100240 1 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100240 1 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x100240 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x100248 [0x48, 0x8B, 0x47, 0x10] (LoadPre 0x100248 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x100248 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100248 0 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100248 0 (.base 7 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x100248 0x48 (by decide) 0 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001f1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001f3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001f5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001f7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001f9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001fa) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100201) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100204) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 69), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100207) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 69), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10020a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 69), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 73), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10020d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 1), (2, 2), (3, 69), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 73), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100217) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (1, 1), (2, 2), (3, 69), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 73), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10021f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 69), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 73), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100229) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 69), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 73), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100231) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 69), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 73), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100234) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 69), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 73), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100238) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 69), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 73), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100240) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 69), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 73), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100248) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 83), (2, 2), (3, 69), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 73), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10024c) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 89) (by decide) rfl

theorem block_l1001f0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1001f0 :=
  Rest.liftedBlock (rest_l1001f0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1001f0 x hx)

theorem rest_l10024c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10024c bytes_l10024c) (entryMap (live .l10024c))
      20 0x10024c bytes_l10024c b_l10024c := by
  have f0 : InstrSpec 0x10024c [0x48, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00] (StorePre 0x10024c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10024c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10024c 0 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10024c 0 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x10024c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x100254 [0x48, 0x8B, 0x47, 0x18] (LoadPre 0x100254 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x100254 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100254 0 (.base 7 (.d8 0x18)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100254 0 (.base 7 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x100254 0x48 (by decide) 0 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100258 [0x48, 0x89, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00] (StorePre 0x100258 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x100258 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100258 0 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100258 0 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x100258 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x100260 [0x48, 0x8B, 0x06] (LoadPre 0x100260 (fun s => AddrMode.addr (.base 6 .none) s (0x100260 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100260 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100260 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x100260 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x100263 [0x48, 0x89, 0x44, 0x24, 0x54] (StorePre 0x100263 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x100263 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100263 0 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100263 0 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_m64_r64_effect_step 0x100263 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x100268 [0x8B, 0x46, 0x08] (LoadPre 0x100268 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x100268 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100268 0 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100268 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x100268 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10026b [0x89, 0x44, 0x24, 0x5C] (StorePre 0x10026b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x10026b + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10026b 0 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10026b 0 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (mov_m32_r32_low_effect_step 0x10026b 0 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10026f [0x48, 0xC7, 0x44, 0x24, 0x61, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10026f 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x61)) s (0x10026f + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10026f (.sib 4 none 0 (.d8 0x61)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10026f (.sib 4 none 0 (.d8 0x61)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10026f 0x48 (by decide) (.sib 4 none 0 (.d8 0x61)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x100278 [0x48, 0xC7, 0x44, 0x24, 0x69, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100278 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x69)) s (0x100278 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100278 (.sib 4 none 0 (.d8 0x69)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100278 (.sib 4 none 0 (.d8 0x69)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100278 0x48 (by decide) (.sib 4 none 0 (.d8 0x69)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x100281 [0x48, 0xC7, 0x44, 0x24, 0x71, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100281 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x71)) s (0x100281 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100281 (.sib 4 none 0 (.d8 0x71)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100281 (.sib 4 none 0 (.d8 0x71)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100281 0x48 (by decide) (.sib 4 none 0 (.d8 0x71)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10028a [0x48, 0xC7, 0x44, 0x24, 0x79, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10028a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x79)) s (0x10028a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10028a (.sib 4 none 0 (.d8 0x79)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10028a (.sib 4 none 0 (.d8 0x79)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10028a 0x48 (by decide) (.sib 4 none 0 (.d8 0x79)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x100293 [0x48, 0xC7, 0x84, 0x24, 0x81, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100293 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x81)) s (0x100293 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100293 (.sib 4 none 0 (.d32 0x81)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100293 (.sib 4 none 0 (.d32 0x81)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100293 0x48 (by decide) (.sib 4 none 0 (.d32 0x81)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10029f [0x48, 0xC7, 0x84, 0x24, 0x89, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10029f 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x89)) s (0x10029f + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10029f (.sib 4 none 0 (.d32 0x89)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10029f (.sib 4 none 0 (.d32 0x89)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10029f 0x48 (by decide) (.sib 4 none 0 (.d32 0x89)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1002ab [0x48, 0xC7, 0x84, 0x24, 0x91, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1002ab 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x91)) s (0x1002ab + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1002ab (.sib 4 none 0 (.d32 0x91)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1002ab (.sib 4 none 0 (.d32 0x91)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1002ab 0x48 (by decide) (.sib 4 none 0 (.d32 0x91)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1002b7 [0x48, 0xC7, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1002b7 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1002b7 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1002b7 (.sib 4 none 0 (.d32 0x98)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1002b7 (.sib 4 none 0 (.d32 0x98)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1002b7 0x48 (by decide) (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1002c3 [0x48, 0x8B, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00] (LoadPre 0x1002c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x1002c3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1002c3 0 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1002c3 0 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_r64_m64_effect_step 0x1002c3 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x1002cb [0x48, 0x89, 0x44, 0x24, 0x48] (StorePre 0x1002cb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1002cb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1002cb 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1002cb 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x1002cb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x1002d0 [0x48, 0x8B, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00] (LoadPre 0x1002d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x1002d0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1002d0 0 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1002d0 0 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x1002d0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x1002d8 [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x1002d8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1002d8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1002d8 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1002d8 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x1002d8 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1002dd [0x48, 0x8B, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00] (LoadPre 0x1002dd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1002dd + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1002dd 0 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1002dd 0 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_r64_m64_effect_step 0x1002dd 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100254) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100258) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100260) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100263) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100268) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10026b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 60), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10026f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 60), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100278) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 60), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100281) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 60), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10028a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 60), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100293) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 60), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10029f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 60), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002ab) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 60), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002b7) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 60), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002c3) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002cb) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002d0) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002d8) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 74), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002dd) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002e5) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 79) (by decide) rfl

theorem block_l10024c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10024c :=
  Rest.liftedBlock (rest_l10024c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10024c x hx)

theorem rest_l1002e5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1002e5 bytes_l1002e5) (entryMap (live .l1002e5))
      20 0x1002e5 bytes_l1002e5 b_l1002e5 := by
  have f0 : InstrSpec 0x1002e5 [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x1002e5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1002e5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1002e5 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1002e5 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x1002e5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1002ea [0x48, 0x8B, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00] (LoadPre 0x1002ea (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1002ea + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1002ea 0 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1002ea 0 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_r64_m64_effect_step 0x1002ea 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1002f2 [0x48, 0x89, 0x44, 0x24, 0x30] (StorePre 0x1002f2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1002f2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1002f2 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1002f2 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1002f2 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1002f7 [0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (LoadPre 0x1002f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1002f7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1002f7 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1002f7 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x1002f7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1002ff [0x48, 0x8B, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x1002ff (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1002ff + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1002ff 1 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1002ff 1 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x1002ff 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x100307 [0x48, 0x89, 0x4C, 0x24, 0x28] (StorePre 0x100307 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100307 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100307 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100307 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x100307 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10030c [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x10030c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10030c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10030c 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10030c 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10030c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x100311 [0xC7, 0x44, 0x24, 0x50, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100311 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x100311 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x100311 8 (.sib 4 none 0 (.d8 0x50)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x100311 8 (.sib 4 none 0 (.d8 0x50)) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x100311 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x100319 [0xC6, 0x44, 0x24, 0x60, 0x40] (StorePre 0x100319 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x100319 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x100319 (.sib 4 none 0 (.d8 0x60)) 0x40)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x100319 (.sib 4 none 0 (.d8 0x60)) 0x40).toInstrSpec (mov_m8_imm8_effect_step 0x100319 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide) 0x40) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10031e [0x48, 0xC7, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10031e 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10031e + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10031e (.sib 4 none 0 (.d32 0xb8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10031e (.sib 4 none 0 (.d32 0xb8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10031e 0x48 (by decide) (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10032a [0x48, 0xC7, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10032a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10032a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10032a (.sib 4 none 0 (.d32 0xb0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10032a (.sib 4 none 0 (.d32 0xb0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10032a 0x48 (by decide) (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x100336 [0x48, 0xC7, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100336 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x100336 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100336 (.sib 4 none 0 (.d32 0xa8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100336 (.sib 4 none 0 (.d32 0xa8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100336 0x48 (by decide) (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x100342 [0x48, 0xC7, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100342 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x100342 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100342 (.sib 4 none 0 (.d32 0xa0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100342 (.sib 4 none 0 (.d32 0xa0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100342 0x48 (by decide) (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x10034e [0x48, 0x8D, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10034e) (leaR64Effect 0x10034e 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x10034e 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x10034e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x100356 [0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x100356 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x100356 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100356 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100356 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x100356 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x10035e [0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x10035e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10035e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10035e 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10035e 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x10035e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x100366 [0x48, 0xC7, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00] (StorePre 0x100366 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x100366 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100366 (.sib 4 none 0 (.d32 0xe0)) 0x20)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100366 (.sib 4 none 0 (.d32 0xe0)) 0x20).toInstrSpec (mov_m64_imm32_effect_step 0x100366 0x48 (by decide) (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide) 0x20) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x100372 [0x48, 0x8D, 0x7C, 0x24, 0x20] (fun s => s.RIP = 0x100372) (leaR64Effect 0x100372 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x100372 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x100372 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x100377 [0x48, 0x8D, 0xB4, 0x24, 0xD0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100377) (leaR64Effect 0x100377 6 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x100377 6 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (lea_r64_effect_step 0x100377 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x10037f [0xE8, 0xFC, 0x06, 0x00, 0x00] (PushPre 0x10037f 5) (callEffect (fun _ => 0x100a80) 0x100384)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10037f 0x100a80 0x100384).toInstrSpec (call_rel32_effect_step 0x10037f 0x6fc (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002ea) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002f2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002f7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002ff) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100307) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10030c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100311) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100319) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10031e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10032a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100336) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100342) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10034e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100356) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10035e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100366) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 69), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100372) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 69), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (7, 74), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100377) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 69), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 76), (7, 74), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10037f) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 69), (1, 59), (2, 2), (3, 3), (4, 78), (5, 5), (6, 76), (7, 74), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a80) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 80) (by decide) (by decide) rfl rfl

theorem block_l1002e5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1002e5 :=
  Rest.liftedBlock (rest_l1002e5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1002e5 x hx)

theorem rest_l100384 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100384 bytes_l100384) (entryMap (live .l100384))
      2 0x100384 bytes_l100384 b_l100384 := by
  have f0 : InstrSpec 0x100384 [0x84, 0xC0] (fun s => s.RIP = 0x100384) (testR8R8Effect 0x100384 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x100384 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x100384 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100386) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x100386 5 0x270) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100384 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100384 :=
  Rest.liftedBlock (rest_l100384 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100384 x hx)

theorem rest_l10038c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10038c bytes_l10038c) (entryMap (live .l10038c))
      5 0x10038c bytes_l10038c b_l10038c := by
  have f0 : InstrSpec 0x10038c [0x49, 0xBF, 0xBF, 0xFF, 0xFF, 0xFF, 0x3F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10038c) (movR64Imm64Effect 0x10038c 15 0x3fffffffbf)
      [] [] [.reg 15, .rip] :=
    (movR64Imm64Effect_footprint 0x10038c 15 0x3fffffffbf).toInstrSpec (mov_r64_imm64_effect_step 0x10038c 0x49 0xbf (by decide) (by decide) 0x3fffffffbf) pre_rip
  have f1 : InstrSpec 0x100396 [0x4C, 0x8D, 0xA4, 0x24, 0x50, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x100396) (leaR64Effect 0x100396 12 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x100396 12 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (lea_r64_effect_step 0x100396 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10039e [0x48, 0x8D, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10039e) (leaR64Effect 0x10039e 6 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10039e 6 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x10039e 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1003a6 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x1003a6) (movR64R64Effect 0x1003a6 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1003a6 7 12).toInstrSpec (mov_r64_r64_effect_step 0x1003a6 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1003a9 [0xE8, 0x92, 0x1A, 0x00, 0x00] (PushPre 0x1003a9 5) (callEffect (fun _ => 0x101e40) 0x1003ae)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1003a9 0x101e40 0x1003ae).toInstrSpec (call_rel32_effect_step 0x1003a9 0x1a92 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100396) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10039e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003a6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003a9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 57), (7, 59), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e40) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10038c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10038c :=
  Rest.liftedBlock (rest_l10038c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10038c x hx)

theorem rest_l1003ae [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1003ae bytes_l1003ae) (entryMap (live .l1003ae))
      11 0x1003ae bytes_l1003ae b_l1003ae := by
  have f0 : InstrSpec 0x1003ae [0xC7, 0x44, 0x24, 0x50, 0x01, 0x00, 0x00, 0x00] (StorePre 0x1003ae 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1003ae + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x1003ae 8 (.sib 4 none 0 (.d8 0x50)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1003ae 8 (.sib 4 none 0 (.d8 0x50)) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x1003ae (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1003b6 [0xC6, 0x44, 0x24, 0x60, 0x40] (StorePre 0x1003b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1003b6 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1003b6 (.sib 4 none 0 (.d8 0x60)) 0x40)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1003b6 (.sib 4 none 0 (.d8 0x60)) 0x40).toInstrSpec (mov_m8_imm8_effect_step 0x1003b6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide) 0x40) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1003bb [0x48, 0x8D, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1003bb) (leaR64Effect 0x1003bb 7 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1003bb 7 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (lea_r64_effect_step 0x1003bb 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1003c3 [0x48, 0x8D, 0x74, 0x24, 0x20] (fun s => s.RIP = 0x1003c3) (leaR64Effect 0x1003c3 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1003c3 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x1003c3 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1003c8 [0xB9, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1003c8) (movR32Imm32Effect 0x1003c8 5 1 0x20)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1003c8 5 1 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x1003c8 0xb9 (by decide) 0x20) pre_rip
  have f5 : InstrSpec 0x1003cd [0xF3, 0xA5] (RepPre 0x1003cd (RepMovsdPre 0x1003cd)) (repMovsdEffect 0x1003cd)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsdEffect_footprint 0x1003cd).toInstrSpecOfRuns (rep_movsd_runs hstride 0x1003cd) (RepMovsOk.of_stateOf RepMovsdPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f6 : InstrSpec 0x1003cf [0x48, 0x8B, 0x4B, 0x10] (LoadPre 0x1003cf (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1003cf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1003cf 1 (.base 3 (.d8 0x10)))
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1003cf 1 (.base 3 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1003cf 0x48 (by decide) 1 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1003d3 [0xB0, 0x01] (fun s => s.RIP = 0x1003d3) (movR8Imm8Effect 0x1003d3 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x1003d3 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x1003d3 0xb0 (by decide) 0x1) pre_rip
  have f8 : InstrSpec 0x1003d5 [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x1003d5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1003d5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1003d5 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1003d5 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1003d5 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1003da [0x4C, 0x39, 0xF9] (fun s => s.RIP = 0x1003da) (cmpR64R64Effect 0x1003da 1 15)
      [.gpr 1, .gpr 15] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1003da 1 15).toInstrSpec (cmp_r64_r64_effect_step 0x1003da 0x4c 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003b6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003bb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003c3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003c8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003cd) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 61), (7, 62), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003cf) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 61), (7, 62), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003d3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 61), (7, 62), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003d5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 61), (7, 62), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003da) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f9 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 66), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 61), (7, 62), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (19, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003dd) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 72) (jcc_rel32_effect_step 0x1003dd 7 0x207) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1003ae [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1003ae :=
  Rest.liftedBlock (rest_l1003ae hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1003ae x hx)

theorem rest_l1003e3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1003e3 bytes_l1003e3) (entryMap (live .l1003e3))
      10 0x1003e3 bytes_l1003e3 b_l1003e3 := by
  have f0 : InstrSpec 0x1003e3 [0x4C, 0x89, 0x6C, 0x24, 0x08] (StorePre 0x1003e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1003e3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1003e3 13 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1003e3 13 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1003e3 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1003e8 [0x4C, 0x89, 0xB4, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x1003e8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1003e8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1003e8 14 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1003e8 14 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x1003e8 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1003f0 [0x48, 0x89, 0x5C, 0x24, 0x10] (StorePre 0x1003f0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1003f0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1003f0 3 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1003f0 3 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1003f0 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1003f5 [0x49, 0xBD, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x1003f5) (movR64Imm64Effect 0x1003f5 13 0x7ffffffffffffff0)
      [] [] [.reg 13, .rip] :=
    (movR64Imm64Effect_footprint 0x1003f5 13 0x7ffffffffffffff0).toInstrSpec (mov_r64_imm64_effect_step 0x1003f5 0x49 0xbd (by decide) (by decide) 0x7ffffffffffffff0) pre_rip
  have f4 : InstrSpec 0x1003ff [0x49, 0x21, 0xED] (fun s => s.RIP = 0x1003ff) (andR64R64Effect 0x1003ff 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1003ff 13 5).toInstrSpec (and_r64_r64_effect_step 0x1003ff 0x49 0xed (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x100402 [0x41, 0x89, 0xEE] (fun s => s.RIP = 0x100402) (movR32R32Effect 0x100402 3 14 5)
      [.gpr 5] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x100402 3 14 5).toInstrSpec (mov_r32_r32_rex_effect_step 0x100402 0x41 0xee (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100405 [0x41, 0x83, 0xE6, 0x0F] (fun s => s.RIP = 0x100405) (andR32Imm8Effect 0x100405 4 14 0xf)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x100405 4 14 0xf).toInstrSpec (and_r32_imm8_rex_effect_step 0x100405 0x41 0xe6 0xf (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100409 [0x48, 0x89, 0xAC, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x100409 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x100409 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100409 5 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100409 5 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x100409 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x100411 [0x48, 0x83, 0xFD, 0x10] (fun s => s.RIP = 0x100411) (cmpR64Imm8Effect 0x100411 5 0x10)
      [.gpr 5] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100411 5 0x10).toInstrSpec (cmp_r64_imm8_effect_step 0x100411 0x48 0xfd 0x10 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003e8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003f0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003f5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (12, 12), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003ff) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (12, 12), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100402) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (12, 12), (13, 58), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100405) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (12, 12), (13, 58), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100409) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (12, 12), (13, 58), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100411) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (12, 12), (13, 58), (14, 62), (15, 15), (16, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100415) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 67) (jcc_rel8_effect_step 0x100415 2 0x1e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1003e3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1003e3 :=
  Rest.liftedBlock (rest_l1003e3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1003e3 x hx)

theorem rest_l100417 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100417 bytes_l100417) (entryMap (live .l100417))
      3 0x100417 bytes_l100417 b_l100417 := by
  have f0 : InstrSpec 0x100417 [0x4C, 0x89, 0xEB] (fun s => s.RIP = 0x100417) (movR64R64Effect 0x100417 3 13)
      [.gpr 13] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x100417 3 13).toInstrSpec (mov_r64_r64_effect_step 0x100417 0x4c 0xeb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10041a [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x10041a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10041a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10041a 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10041a 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10041a 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10041f [0x90] (fun s => s.RIP = 0x10041f) (fun _ => nopEffect 0x10041f 1)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10041f 1).toInstrSpec (nop_effect_step 0x10041f) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 53), (4, 4), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10041a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 53), (4, 4), (6, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10041f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(2, 2), (3, 53), (4, 4), (6, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100420) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l100417 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100417 :=
  Rest.liftedBlock (rest_l100417 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100417 x hx)

theorem rest_l100420 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100420 bytes_l100420) (entryMap (live .l100420))
      3 0x100420 bytes_l100420 b_l100420 := by
  have f0 : InstrSpec 0x100420 [0x48, 0x8D, 0x6E, 0x10] (fun s => s.RIP = 0x100420) (leaR64Effect 0x100420 5 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x100420 5 (.base 6 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x100420 0x48 (by decide) 5 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100424 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x100424) (movR64R64Effect 0x100424 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x100424 7 12).toInstrSpec (mov_r64_r64_effect_step 0x100424 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100427 [0xE8, 0x04, 0x1A, 0x00, 0x00] (PushPre 0x100427 5) (callEffect (fun _ => 0x101e30) 0x10042c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100427 0x101e30 0x10042c).toInstrSpec (call_rel32_effect_step 0x100427 0x1a04 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100424) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100427) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 53), (6, 6), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e30) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l100420 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100420 :=
  Rest.liftedBlock (rest_l100420 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100420 x hx)

theorem rest_l10042c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10042c bytes_l10042c) (entryMap (live .l10042c))
      3 0x10042c bytes_l10042c b_l10042c := by
  have f0 : InstrSpec 0x10042c [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x10042c) (movR64R64Effect 0x10042c 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10042c 6 5).toInstrSpec (mov_r64_r64_effect_step 0x10042c 0x48 0xee (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10042f [0x48, 0x83, 0xC3, 0xF0] (fun s => s.RIP = 0x10042f) (addR64Imm8Effect 0x10042f 3 0xf0)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10042f 3 0xf0).toInstrSpec (add_r64_imm8_effect_step 0x10042f 0x48 0xc3 0xf0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10042f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (3, 55), (4, 4), (5, 5), (6, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100433) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x100433 5 0xeb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10042c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10042c :=
  Rest.liftedBlock (rest_l10042c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10042c x hx)

theorem rest_l100435 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100435 bytes_l100435) (entryMap (live .l100435))
      2 0x100435 bytes_l100435 b_l100435 := by
  have f0 : InstrSpec 0x100435 [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x100435) (testR64R64Effect 0x100435 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x100435 14 14).toInstrSpec (test_r64_r64_effect_step 0x100435 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100438) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x100438 4 0x3f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100435 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100435 :=
  Rest.liftedBlock (rest_l100435 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100435 x hx)

theorem rest_l10043a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10043a bytes_l10043a) (entryMap (live .l10043a))
      8 0x10043a bytes_l10043a b_l10043a := by
  have f0 : InstrSpec 0x10043a [0x48, 0x8B, 0x6C, 0x24, 0x08] (LoadPre 0x10043a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10043a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10043a 5 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x10043a 5 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10043a 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10043f [0x4C, 0x01, 0xED] (fun s => s.RIP = 0x10043f) (addR64R64Effect 0x10043f 5 13)
      [.gpr 5, .gpr 13] [] [.reg 5, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10043f 5 13).toInstrSpec (add_r64_r64_effect_step 0x10043f 0x4c 0xed (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100442 [0xBA, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100442) (movR32Imm32Effect 0x100442 5 2 0x10)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x100442 5 2 0x10).toInstrSpec (mov_r32_imm32_effect_step 0x100442 0xba (by decide) 0x10) pre_rip
  have f3 : InstrSpec 0x100447 [0x4C, 0x29, 0xF2] (fun s => s.RIP = 0x100447) (subR64R64Effect 0x100447 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x100447 2 14).toInstrSpec (sub_r64_r64_effect_step 0x100447 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10044a [0x4A, 0x8D, 0x3C, 0x34] (fun s => s.RIP = 0x10044a) (leaR64Effect 0x10044a 7 (.sib 4 (some 14) 0 .none))
      [.gpr 4, .gpr 14] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10044a 7 (.sib 4 (some 14) 0 .none)).toInstrSpec (lea_r64_effect_step 0x10044a 0x4a (by decide) 7 (.sib 4 (some 14) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10044e [0x48, 0x83, 0xC7, 0x20] (fun s => s.RIP = 0x10044e) (addR64Imm8Effect 0x10044e 7 0x20)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10044e 7 0x20).toInstrSpec (add_r64_imm8_effect_step 0x10044e 0x48 0xc7 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100452 [0x31, 0xF6] (fun s => s.RIP = 0x100452) (xorR32R32Effect 0x100452 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100452 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x100452 0xf6 (by decide)) pre_rip
  have f7 : InstrSpec 0x100454 [0xFF, 0x15, 0x86, 0x0F, 0x10, 0x00] (GoesTo (CallMemPre 0x100454 (.rip 0x100f86)) (callEffect (callMemPtr 0x100454 (.rip 0x100f86)) (0x100454 + BitVec.ofNat 64 (callMemLen (.rip 0x100f86)))) 0x102d70) (callEffect (callMemPtr 0x100454 (.rip 0x100f86)) (0x100454 + BitVec.ofNat 64 (callMemLen (.rip 0x100f86))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x100454 (.rip 0x100f86)).toInstrSpec (call_m64_effect_step 0x100454 (.rip 0x100f86) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x102d70
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 53), (6, 6), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10043f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 55), (6, 6), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100442) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 55), (6, 6), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100447) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 55), (6, 6), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10044a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 55), (6, 6), (7, 61), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10044e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 55), (6, 6), (7, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100452) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 55), (6, 65), (7, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100454) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 59), (3, 3), (4, 67), (5, 55), (6, 65), (7, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d70) f7 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l10043a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10043a :=
  Rest.liftedBlock (rest_l10043a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10043a x hx)

theorem rest_l10045a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10045a bytes_l10045a) (entryMap (live .l10045a))
      5 0x10045a bytes_l10045a b_l10045a := by
  have f0 : InstrSpec 0x10045a [0x48, 0x8D, 0x5C, 0x24, 0x20] (fun s => s.RIP = 0x10045a) (leaR64Effect 0x10045a 3 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x10045a 3 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x10045a 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10045f [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x10045f) (movR64R64Effect 0x10045f 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10045f 7 3).toInstrSpec (mov_r64_r64_effect_step 0x10045f 0x48 0xdf (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100462 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x100462) (movR64R64Effect 0x100462 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100462 6 5).toInstrSpec (mov_r64_r64_effect_step 0x100462 0x48 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100465 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x100465) (movR64R64Effect 0x100465 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x100465 2 14).toInstrSpec (mov_r64_r64_effect_step 0x100465 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100468 [0xFF, 0x15, 0x3A, 0x0F, 0x10, 0x00] (GoesTo (CallMemPre 0x100468 (.rip 0x100f3a)) (callEffect (callMemPtr 0x100468 (.rip 0x100f3a)) (0x100468 + BitVec.ofNat 64 (callMemLen (.rip 0x100f3a)))) 0x102dc0) (callEffect (callMemPtr 0x100468 (.rip 0x100f3a)) (0x100468 + BitVec.ofNat 64 (callMemLen (.rip 0x100f3a))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x100468 (.rip 0x100f3a)).toInstrSpec (call_m64_effect_step 0x100468 (.rip 0x100f3a) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x102dc0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10045f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100462) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100465) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 53), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100468) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 53), (4, 61), (5, 5), (6, 57), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dc0) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10045a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10045a :=
  Rest.liftedBlock (rest_l10045a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10045a x hx)

theorem rest_l10046e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10046e bytes_l10046e) (entryMap (live .l10046e))
      3 0x10046e bytes_l10046e b_l10046e := by
  have f0 : InstrSpec 0x10046e [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x10046e) (movR64R64Effect 0x10046e 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10046e 7 12).toInstrSpec (mov_r64_r64_effect_step 0x10046e 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100471 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x100471) (movR64R64Effect 0x100471 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100471 6 3).toInstrSpec (mov_r64_r64_effect_step 0x100471 0x48 0xde (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100474 [0xE8, 0xB7, 0x19, 0x00, 0x00] (PushPre 0x100474 5) (callEffect (fun _ => 0x101e30) 0x100479)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100474 0x101e30 0x100479).toInstrSpec (call_rel32_effect_step 0x100474 0x19b7 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100471) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100474) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e30) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l10046e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10046e :=
  Rest.liftedBlock (rest_l10046e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10046e x hx)

theorem rest_l100479 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100479 bytes_l100479) (entryMap (live .l100479))
      9 0x100479 bytes_l100479 b_l100479 := by
  have f0 : InstrSpec 0x100479 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x100479 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100479 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100479 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100479 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x100479 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10047e [0x4C, 0x8B, 0x28] (LoadPre 0x10047e (fun s => AddrMode.addr (.base 0 .none) s (0x10047e + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10047e 13 (.base 0 .none))
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x10047e 13 (.base 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10047e 0x4c (by decide) 5 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100481 [0x49, 0x83, 0xC7, 0x31] (fun s => s.RIP = 0x100481) (addR64Imm8Effect 0x100481 15 0x31)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x100481 15 0x31).toInstrSpec (add_r64_imm8_effect_step 0x100481 0x49 0xc7 0x31 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100485 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x100485 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100485 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100485 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100485 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x100485 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10048a [0x49, 0x21, 0xC7] (fun s => s.RIP = 0x10048a) (andR64R64Effect 0x10048a 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10048a 15 0).toInstrSpec (and_r64_r64_effect_step 0x10048a 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10048d [0x41, 0x89, 0xC6] (fun s => s.RIP = 0x10048d) (movR32R32Effect 0x10048d 3 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x10048d 3 14 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x10048d 0x41 0xc6 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100490 [0x41, 0x83, 0xE6, 0x0F] (fun s => s.RIP = 0x100490) (andR32Imm8Effect 0x100490 4 14 0xf)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x100490 4 14 0xf).toInstrSpec (and_r32_imm8_rex_effect_step 0x100490 0x41 0xe6 0xf (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100494 [0x48, 0x83, 0xF8, 0x10] (fun s => s.RIP = 0x100494) (cmpR64Imm8Effect 0x100494 0 0x10)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100494 0 0x10).toInstrSpec (cmp_r64_imm8_effect_step 0x100494 0x48 0xf8 0x10 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10047e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (12, 12), (13, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100481) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (12, 12), (13, 55), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100485) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (12, 12), (13, 55), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10048a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (12, 12), (13, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10048d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (12, 12), (13, 55), (14, 63), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100490) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (12, 12), (13, 55), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100494) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (12, 12), (13, 55), (14, 65), (15, 61), (16, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100498) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 69) (jcc_rel8_effect_step 0x100498 2 0x1b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100479 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100479 :=
  Rest.liftedBlock (rest_l100479 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100479 x hx)

theorem rest_l10049a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10049a bytes_l10049a) (entryMap (live .l10049a))
      2 0x10049a bytes_l10049a b_l10049a := by
  have f0 : InstrSpec 0x10049a [0x4C, 0x89, 0xFB] (fun s => s.RIP = 0x10049a) (movR64R64Effect 0x10049a 3 15)
      [.gpr 15] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10049a 3 15).toInstrSpec (mov_r64_r64_effect_step 0x10049a 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10049d [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x10049d) (movR64R64Effect 0x10049d 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10049d 6 13).toInstrSpec (mov_r64_r64_effect_step 0x10049d 0x4c 0xee (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 53), (4, 4), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10049d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 53), (4, 4), (6, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004a0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l10049a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10049a :=
  Rest.liftedBlock (rest_l10049a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10049a x hx)

theorem rest_l1004a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1004a0 bytes_l1004a0) (entryMap (live .l1004a0))
      3 0x1004a0 bytes_l1004a0 b_l1004a0 := by
  have f0 : InstrSpec 0x1004a0 [0x48, 0x8D, 0x6E, 0x10] (fun s => s.RIP = 0x1004a0) (leaR64Effect 0x1004a0 5 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x1004a0 5 (.base 6 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1004a0 0x48 (by decide) 5 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1004a4 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x1004a4) (movR64R64Effect 0x1004a4 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1004a4 7 12).toInstrSpec (mov_r64_r64_effect_step 0x1004a4 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1004a7 [0xE8, 0x84, 0x19, 0x00, 0x00] (PushPre 0x1004a7 5) (callEffect (fun _ => 0x101e30) 0x1004ac)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1004a7 0x101e30 0x1004ac).toInstrSpec (call_rel32_effect_step 0x1004a7 0x1984 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004a4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004a7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 53), (6, 6), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e30) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l1004a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1004a0 :=
  Rest.liftedBlock (rest_l1004a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1004a0 x hx)

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

theorem_by block_l1001f0_eval :
    program.runBlock (dialect code) ⟨.l1001f0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10024c_eval :
    program.runBlock (dialect code) ⟨.l10024c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1002e5_eval :
    program.runBlock (dialect code) ⟨.l1002e5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100384_eval :
    program.runBlock (dialect code) ⟨.l100384, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10038c_eval :
    program.runBlock (dialect code) ⟨.l10038c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1003ae_eval :
    program.runBlock (dialect code) ⟨.l1003ae, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1003e3_eval :
    program.runBlock (dialect code) ⟨.l1003e3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100417_eval :
    program.runBlock (dialect code) ⟨.l100417, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100420_eval :
    program.runBlock (dialect code) ⟨.l100420, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10042c_eval :
    program.runBlock (dialect code) ⟨.l10042c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100435_eval :
    program.runBlock (dialect code) ⟨.l100435, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10043a_eval :
    program.runBlock (dialect code) ⟨.l10043a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10045a_eval :
    program.runBlock (dialect code) ⟨.l10045a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10046e_eval :
    program.runBlock (dialect code) ⟨.l10046e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100479_eval :
    program.runBlock (dialect code) ⟨.l100479, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10049a_eval :
    program.runBlock (dialect code) ⟨.l10049a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1004a0_eval :
    program.runBlock (dialect code) ⟨.l1004a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
