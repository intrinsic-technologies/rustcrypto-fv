import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l1057c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1057c0 bytes_l1057c0) (entryMap (live .l1057c0))
      14 0x1057c0 bytes_l1057c0 b_l1057c0 := by
  have f0 : InstrSpec 0x1057c0 [0x55] (PushPre 0x1057c0 1) (pushR64Effect 0x1057c0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1057c0 1 5).toInstrSpec (push_r64_effect_step 0x1057c0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1057c1 [0x41, 0x57] (PushPre 0x1057c1 2) (pushR64Effect 0x1057c1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1057c1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1057c1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1057c3 [0x41, 0x56] (PushPre 0x1057c3 2) (pushR64Effect 0x1057c3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1057c3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1057c3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1057c5 [0x41, 0x55] (PushPre 0x1057c5 2) (pushR64Effect 0x1057c5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1057c5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1057c5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1057c7 [0x41, 0x54] (PushPre 0x1057c7 2) (pushR64Effect 0x1057c7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1057c7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1057c7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1057c9 [0x53] (PushPre 0x1057c9 1) (pushR64Effect 0x1057c9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1057c9 1 3).toInstrSpec (push_r64_effect_step 0x1057c9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1057ca [0x48, 0x81, 0xEC, 0x38, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1057ca) (subR64Imm32Effect 0x1057ca 4 0x138)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x1057ca 4 0x138).toInstrSpec (sub_r64_imm32_effect_step 0x1057ca 0x48 0xec 0x138 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1057d1 [0x49, 0x89, 0xF4] (fun s => s.RIP = 0x1057d1) (movR64R64Effect 0x1057d1 12 6)
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x1057d1 12 6).toInstrSpec (mov_r64_r64_effect_step 0x1057d1 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1057d4 [0x48, 0x89, 0xBC, 0x24, 0x30, 0x01, 0x00, 0x00] (StorePre 0x1057d4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x1057d4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1057d4 7 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1057d4 7 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_m64_r64_effect_step 0x1057d4 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1057dc [0x4C, 0x8D, 0x74, 0x24, 0x0C] (fun s => s.RIP = 0x1057dc) (leaR64Effect 0x1057dc 14 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x1057dc 14 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (lea_r64_effect_step 0x1057dc 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1057e1 [0xBA, 0xF0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1057e1) (movR32Imm32Effect 0x1057e1 5 2 0xf0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1057e1 5 2 0xf0).toInstrSpec (mov_r32_imm32_effect_step 0x1057e1 0xba (by decide) 0xf0) pre_rip
  have f11 : InstrSpec 0x1057e6 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x1057e6) (movR64R64Effect 0x1057e6 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1057e6 7 14).toInstrSpec (mov_r64_r64_effect_step 0x1057e6 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1057e9 [0x31, 0xF6] (fun s => s.RIP = 0x1057e9) (xorR32R32Effect 0x1057e9 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1057e9 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x1057e9 0xf6 (by decide)) pre_rip
  have f13 : InstrSpec 0x1057eb [0xFF, 0x15, 0x37, 0xBA, 0x0F, 0x00] (GoesTo (CallMemPre 0x1057eb (.rip 0xfba37)) (callEffect (callMemPtr 0x1057eb (.rip 0xfba37)) (0x1057eb + BitVec.ofNat 64 (callMemLen (.rip 0xfba37)))) 0x103eb0) (callEffect (callMemPtr 0x1057eb (.rip 0xfba37)) (0x1057eb + BitVec.ofNat 64 (callMemLen (.rip 0xfba37))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1057eb (.rip 0xfba37)).toInstrSpec (call_m64_effect_step 0x1057eb (.rip 0xfba37) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103eb0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057c3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057c5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057c7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057c9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057ca) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057d1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057d4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057dc) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057e1) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(2, 72), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057e6) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(2, 72), (3, 3), (4, 65), (5, 5), (6, 6), (7, 74), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057e9) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(2, 72), (3, 3), (4, 65), (5, 5), (6, 76), (7, 74), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057eb) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(2, 72), (3, 3), (4, 78), (5, 5), (6, 76), (7, 74), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eb0) f13 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 80) (by decide) (by decide) rfl rfl

theorem block_l1057c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1057c0 :=
  Rest.liftedBlock (rest_l1057c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1057c0 x hx)

theorem rest_l1057f1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1057f1 bytes_l1057f1) (entryMap (live .l1057f1))
      9 0x1057f1 bytes_l1057f1 b_l1057f1 := by
  have f0 : InstrSpec 0x1057f1 [0x49, 0x8B, 0x04, 0x24] (LoadPre 0x1057f1 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x1057f1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1057f1 0 (.sib 12 none 0 .none))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1057f1 0 (.sib 12 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1057f1 0x49 (by decide) 0 (.sib 12 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1057f5 [0x49, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x1057f5 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x1057f5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1057f5 1 (.sib 12 none 0 (.d8 0x8)))
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1057f5 1 (.sib 12 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1057f5 0x49 (by decide) 1 (.sib 12 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1057fa [0x48, 0x89, 0x8C, 0x24, 0x28, 0x01, 0x00, 0x00] (StorePre 0x1057fa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x1057fa + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1057fa 1 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1057fa 1 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_m64_r64_effect_step 0x1057fa 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x105802 [0x48, 0x89, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00] (StorePre 0x105802 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x105802 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105802 0 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105802 0 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_m64_r64_effect_step 0x105802 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10580a [0x41, 0xBF, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10580a) (movR32Imm32Effect 0x10580a 6 15 0x8)
      [] [] [.reg 15, .rip] :=
    (movR32Imm32Effect_footprint 0x10580a 6 15 0x8).toInstrSpec (mov_r32_imm32_rex_effect_step 0x10580a 0x41 0xbf (by decide) (by decide) 0x8) pre_rip
  have f5 : InstrSpec 0x105810 [0x48, 0x8D, 0x94, 0x24, 0x20, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105810) (leaR64Effect 0x105810 2 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x105810 2 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (lea_r64_effect_step 0x105810 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x105818 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105818) (movR32Imm32Effect 0x105818 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x105818 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x105818 0xbe (by decide) 0x8) pre_rip
  have f7 : InstrSpec 0x10581d [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10581d) (movR64R64Effect 0x10581d 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10581d 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10581d 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x105820 [0xE8, 0xCB, 0x47, 0x00, 0x00] (PushPre 0x105820 5) (callEffect (fun _ => 0x109ff0) 0x105825)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105820 0x109ff0 0x105825).toInstrSpec (call_rel32_effect_step 0x105820 0x47cb (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057f5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057fa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105802) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10580a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105810) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 55), (2, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105818) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 63), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10581d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105820) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 55), (2, 61), (3, 3), (4, 67), (5, 5), (6, 63), (7, 65), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ff0) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l1057f1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1057f1 :=
  Rest.liftedBlock (rest_l1057f1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1057f1 x hx)

theorem rest_l105825 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105825 bytes_l105825) (entryMap (live .l105825))
      8 0x105825 bytes_l105825 b_l105825 := by
  have f0 : InstrSpec 0x105825 [0x48, 0x8D, 0x7C, 0x24, 0x1C] (fun s => s.RIP = 0x105825) (leaR64Effect 0x105825 7 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x105825 7 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (lea_r64_effect_step 0x105825 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10582a [0x49, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x10582a (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x10582a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10582a 0 (.sib 12 none 0 (.d8 0x10)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10582a 0 (.sib 12 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10582a 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10582f [0x49, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x10582f (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x10582f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10582f 1 (.sib 12 none 0 (.d8 0x18)))
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10582f 1 (.sib 12 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10582f 0x49 (by decide) 1 (.sib 12 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x105834 [0x48, 0x89, 0x8C, 0x24, 0x28, 0x01, 0x00, 0x00] (StorePre 0x105834 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x105834 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105834 1 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105834 1 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_m64_r64_effect_step 0x105834 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10583c [0x48, 0x89, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00] (StorePre 0x10583c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10583c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10583c 0 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10583c 0 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_m64_r64_effect_step 0x10583c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x105844 [0x48, 0x8D, 0x94, 0x24, 0x20, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105844) (leaR64Effect 0x105844 2 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x105844 2 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (lea_r64_effect_step 0x105844 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10584c [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10584c) (movR32Imm32Effect 0x10584c 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10584c 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x10584c 0xbe (by decide) 0x8) pre_rip
  have f7 : InstrSpec 0x105851 [0xE8, 0x9A, 0x47, 0x00, 0x00] (PushPre 0x105851 5) (callEffect (fun _ => 0x109ff0) 0x105856)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105851 0x109ff0 0x105856).toInstrSpec (call_rel32_effect_step 0x105851 0x479a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10582a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10582f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105834) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10583c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105844) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 57), (2, 61), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10584c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 57), (2, 61), (3, 3), (4, 4), (5, 5), (6, 63), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105851) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 57), (2, 61), (3, 3), (4, 65), (5, 5), (6, 63), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ff0) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l105825 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105825 :=
  Rest.liftedBlock (rest_l105825 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105825 x hx)

theorem rest_l105856 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105856 bytes_l105856) (entryMap (live .l105856))
      4 0x105856 bytes_l105856 b_l105856 := by
  have f0 : InstrSpec 0x105856 [0xBB, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105856) (movR32Imm32Effect 0x105856 5 3 0x20)
      [] [] [.reg 3, .rip] :=
    (movR32Imm32Effect_footprint 0x105856 5 3 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x105856 0xbb (by decide) 0x20) pre_rip
  have f1 : InstrSpec 0x10585b [0x41, 0xBC, 0x30, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10585b) (movR32Imm32Effect 0x10585b 6 12 0x30)
      [] [] [.reg 12, .rip] :=
    (movR32Imm32Effect_footprint 0x10585b 6 12 0x30).toInstrSpec (mov_r32_imm32_rex_effect_step 0x10585b 0x41 0xbc (by decide) (by decide) 0x30) pre_rip
  have f2 : InstrSpec 0x105861 [0x41, 0xBD, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105861) (movR32Imm32Effect 0x105861 6 13 0x20)
      [] [] [.reg 13, .rip] :=
    (movR32Imm32Effect_footprint 0x105861 6 13 0x20).toInstrSpec (mov_r32_imm32_rex_effect_step 0x105861 0x41 0xbd (by decide) (by decide) 0x20) pre_rip
  have f3 : InstrSpec 0x105867 [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105867) (fun _ => nopEffect 0x105867 9)
      [] [] [.rip] :=
    (nopEffect_footprint 0x105867 9).toInstrSpec (nop_m_effect_step 0x105867 [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10585b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105861) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 55), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105867) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 55), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105870) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l105856 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105856 :=
  Rest.liftedBlock (rest_l105856 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105856 x hx)

theorem rest_l105870 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105870 bytes_l105870) (entryMap (live .l105870))
      4 0x105870 bytes_l105870 b_l105870 := by
  have f0 : InstrSpec 0x105870 [0xBE, 0x78, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105870) (movR32Imm32Effect 0x105870 5 6 0x78)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x105870 5 6 0x78).toInstrSpec (mov_r32_imm32_effect_step 0x105870 0xbe (by decide) 0x78) pre_rip
  have f1 : InstrSpec 0x105875 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x105875) (movR64R64Effect 0x105875 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105875 7 14).toInstrSpec (mov_r64_r64_effect_step 0x105875 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x105878 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x105878) (movR64R64Effect 0x105878 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x105878 2 15).toInstrSpec (mov_r64_r64_effect_step 0x105878 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10587b [0xE8, 0xB0, 0xE6, 0xFF, 0xFF] (PushPre 0x10587b 5) (callEffect (fun _ => 0x103f30) 0x105880)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10587b 0x103f30 0x105880).toInstrSpec (call_rel32_effect_step 0x10587b 0xffffe6b0 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105875) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105878) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10587b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f30) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l105870 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105870 :=
  Rest.liftedBlock (rest_l105870 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105870 x hx)

theorem rest_l105880 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105880 bytes_l105880) (entryMap (live .l105880))
      4 0x105880 bytes_l105880 b_l105880 := by
  have f0 : InstrSpec 0x105880 [0x48, 0x8D, 0x3C, 0x1C] (fun s => s.RIP = 0x105880) (leaR64Effect 0x105880 7 (.sib 4 (some 3) 0 .none))
      [.gpr 4, .gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x105880 7 (.sib 4 (some 3) 0 .none)).toInstrSpec (lea_r64_effect_step 0x105880 0x48 (by decide) 7 (.sib 4 (some 3) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105884 [0x48, 0x83, 0xC7, 0x0C] (fun s => s.RIP = 0x105884) (addR64Imm8Effect 0x105884 7 0xc)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x105884 7 0xc).toInstrSpec (add_r64_imm8_effect_step 0x105884 0x48 0xc7 0xc (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x105888 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105888) (movR32Imm32Effect 0x105888 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x105888 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x105888 0xbe (by decide) 0x8) pre_rip
  have f3 : InstrSpec 0x10588d [0xE8, 0x7E, 0xB2, 0xFF, 0xFF] (PushPre 0x10588d 5) (callEffect (fun _ => 0x100b10) 0x105892)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10588d 0x100b10 0x105892).toInstrSpec (call_rel32_effect_step 0x10588d 0xffffb27e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105884) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105888) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10588d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b10) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l105880 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105880 :=
  Rest.liftedBlock (rest_l105880 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105880 x hx)

theorem rest_l105892 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105892 bytes_l105892) (entryMap (live .l105892))
      12 0x105892 bytes_l105892 b_l105892 := by
  have f0 : InstrSpec 0x105892 [0x66, 0xF7, 0x54, 0x1C, 0x0C] (StorePre 0x105892 5 (fun s => AddrMode.addr (.sib 4 (some 3) 0 (.d8 0xc)) s (0x105892 + BitVec.ofNat 64 5)) 2) (notMEffect 0x105892 5 16 (.sib 4 (some 3) 0 (.d8 0xc)))
      [.gpr 4, .gpr 3] [] [.rip] :=
    (notMEffect16_footprint 0x105892 5 (.sib 4 (some 3) 0 (.d8 0xc))).toInstrSpec (not_m16_effect_step 0x105892 (.sib 4 (some 3) 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x105897 [0x66, 0xF7, 0x54, 0x1C, 0x0E] (StorePre 0x105897 5 (fun s => AddrMode.addr (.sib 4 (some 3) 0 (.d8 0xe)) s (0x105897 + BitVec.ofNat 64 5)) 2) (notMEffect 0x105897 5 16 (.sib 4 (some 3) 0 (.d8 0xe)))
      [.gpr 4, .gpr 3] [] [.rip] :=
    (notMEffect16_footprint 0x105897 5 (.sib 4 (some 3) 0 (.d8 0xe))).toInstrSpec (not_m16_effect_step 0x105897 (.sib 4 (some 3) 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10589c [0x66, 0xF7, 0x54, 0x1C, 0x16] (StorePre 0x10589c 5 (fun s => AddrMode.addr (.sib 4 (some 3) 0 (.d8 0x16)) s (0x10589c + BitVec.ofNat 64 5)) 2) (notMEffect 0x10589c 5 16 (.sib 4 (some 3) 0 (.d8 0x16)))
      [.gpr 4, .gpr 3] [] [.rip] :=
    (notMEffect16_footprint 0x10589c 5 (.sib 4 (some 3) 0 (.d8 0x16))).toInstrSpec (not_m16_effect_step 0x10589c (.sib 4 (some 3) 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1058a1 [0x66, 0xF7, 0x54, 0x1C, 0x18] (StorePre 0x1058a1 5 (fun s => AddrMode.addr (.sib 4 (some 3) 0 (.d8 0x18)) s (0x1058a1 + BitVec.ofNat 64 5)) 2) (notMEffect 0x1058a1 5 16 (.sib 4 (some 3) 0 (.d8 0x18)))
      [.gpr 4, .gpr 3] [] [.rip] :=
    (notMEffect16_footprint 0x1058a1 5 (.sib 4 (some 3) 0 (.d8 0x18))).toInstrSpec (not_m16_effect_step 0x1058a1 (.sib 4 (some 3) 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1058a6 [0x42, 0x80, 0x74, 0x2C, 0x0C, 0x80] (StorePre 0x1058a6 6 (fun s => AddrMode.addr (.sib 4 (some 13) 0 (.d8 0xc)) s (0x1058a6 + BitVec.ofNat 64 6)) 1) (xorM8Imm8Effect 0x1058a6 6 (.sib 4 (some 13) 0 (.d8 0xc)) 0x80)
      [.gpr 4, .gpr 13] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x1058a6 6 (.sib 4 (some 13) 0 (.d8 0xc)) 0x80).toInstrSpec (xor_m8_imm8_rex_effect_step 0x1058a6 0x42 (by decide) (.sib 4 (some 13) 0 (.d8 0xc)) (by decide) (by decide) (by decide) 0x80) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1058ac [0x49, 0x83, 0xC7, 0x08] (fun s => s.RIP = 0x1058ac) (addR64Imm8Effect 0x1058ac 15 0x8)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1058ac 15 0x8).toInstrSpec (add_r64_imm8_effect_step 0x1058ac 0x49 0xc7 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1058b0 [0xBE, 0x78, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1058b0) (movR32Imm32Effect 0x1058b0 5 6 0x78)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1058b0 5 6 0x78).toInstrSpec (mov_r32_imm32_effect_step 0x1058b0 0xbe (by decide) 0x78) pre_rip
  have f7 : InstrSpec 0x1058b5 [0xB9, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1058b5) (movR32Imm32Effect 0x1058b5 5 1 0x10)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1058b5 5 1 0x10).toInstrSpec (mov_r32_imm32_effect_step 0x1058b5 0xb9 (by decide) 0x10) pre_rip
  have f8 : InstrSpec 0x1058ba [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x1058ba) (movR64R64Effect 0x1058ba 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1058ba 7 14).toInstrSpec (mov_r64_r64_effect_step 0x1058ba 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1058bd [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x1058bd) (movR64R64Effect 0x1058bd 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1058bd 2 15).toInstrSpec (mov_r64_r64_effect_step 0x1058bd 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1058c0 [0x41, 0xB8, 0x07, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1058c0) (movR32Imm32Effect 0x1058c0 6 8 0x7)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x1058c0 6 8 0x7).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1058c0 0x41 0xb8 (by decide) (by decide) 0x7) pre_rip
  have f11 : InstrSpec 0x1058c6 [0xE8, 0x45, 0xE7, 0xFF, 0xFF] (PushPre 0x1058c6 5) (callEffect (fun _ => 0x104010) 0x1058cb)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1058c6 0x104010 0x1058cb).toInstrSpec (call_rel32_effect_step 0x1058c6 0xffffe745 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105897) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10589c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058a1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058a6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058ac) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058b0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 60), (11, 11), (12, 12), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058b5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 62), (3, 3), (4, 4), (5, 5), (6, 60), (11, 11), (12, 12), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058ba) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 62), (3, 3), (4, 4), (5, 5), (6, 60), (7, 64), (11, 11), (12, 12), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058bd) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 62), (2, 66), (3, 3), (4, 4), (5, 5), (6, 60), (7, 64), (11, 11), (12, 12), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058c0) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 62), (2, 66), (3, 3), (4, 4), (5, 5), (6, 60), (7, 64), (8, 68), (11, 11), (12, 12), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058c6) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 62), (2, 66), (3, 3), (4, 70), (5, 5), (6, 60), (7, 64), (8, 68), (11, 11), (12, 12), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104010) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 72) (by decide) (by decide) rfl rfl

theorem block_l105892 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105892 :=
  Rest.liftedBlock (rest_l105892 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105892 x hx)

theorem rest_l1058cb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1058cb bytes_l1058cb) (entryMap (live .l1058cb))
      2 0x1058cb bytes_l1058cb b_l1058cb := by
  have f0 : InstrSpec 0x1058cb [0x49, 0x81, 0xFD, 0xEC, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1058cb) (cmpR64Imm32Effect 0x1058cb 13 0xec)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR64Imm32Effect_footprint 0x1058cb 13 0xec).toInstrSpec (cmp_r64_imm32_effect_step 0x1058cb 0x49 0xfd 0xec (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058d2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1058d2 4 0x66) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1058cb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1058cb :=
  Rest.liftedBlock (rest_l1058cb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1058cb x hx)

theorem rest_l1058d4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1058d4 bytes_l1058d4) (entryMap (live .l1058d4))
      4 0x1058d4 bytes_l1058d4 b_l1058d4 := by
  have f0 : InstrSpec 0x1058d4 [0xBE, 0x78, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1058d4) (movR32Imm32Effect 0x1058d4 5 6 0x78)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1058d4 5 6 0x78).toInstrSpec (mov_r32_imm32_effect_step 0x1058d4 0xbe (by decide) 0x78) pre_rip
  have f1 : InstrSpec 0x1058d9 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x1058d9) (movR64R64Effect 0x1058d9 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1058d9 7 14).toInstrSpec (mov_r64_r64_effect_step 0x1058d9 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1058dc [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x1058dc) (movR64R64Effect 0x1058dc 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1058dc 2 15).toInstrSpec (mov_r64_r64_effect_step 0x1058dc 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1058df [0xE8, 0x4C, 0xE6, 0xFF, 0xFF] (PushPre 0x1058df 5) (callEffect (fun _ => 0x103f30) 0x1058e4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1058df 0x103f30 0x1058e4).toInstrSpec (call_rel32_effect_step 0x1058df 0xffffe64c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058d9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058dc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058df) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f30) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1058d4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1058d4 :=
  Rest.liftedBlock (rest_l1058d4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1058d4 x hx)

theorem rest_l1058e4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1058e4 bytes_l1058e4) (entryMap (live .l1058e4))
      4 0x1058e4 bytes_l1058e4 b_l1058e4 := by
  have f0 : InstrSpec 0x1058e4 [0x4A, 0x8D, 0x3C, 0x24] (fun s => s.RIP = 0x1058e4) (leaR64Effect 0x1058e4 7 (.sib 4 (some 12) 0 .none))
      [.gpr 4, .gpr 12] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1058e4 7 (.sib 4 (some 12) 0 .none)).toInstrSpec (lea_r64_effect_step 0x1058e4 0x4a (by decide) 7 (.sib 4 (some 12) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1058e8 [0x48, 0x83, 0xC7, 0x0C] (fun s => s.RIP = 0x1058e8) (addR64Imm8Effect 0x1058e8 7 0xc)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1058e8 7 0xc).toInstrSpec (add_r64_imm8_effect_step 0x1058e8 0x48 0xc7 0xc (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1058ec [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1058ec) (movR32Imm32Effect 0x1058ec 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1058ec 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x1058ec 0xbe (by decide) 0x8) pre_rip
  have f3 : InstrSpec 0x1058f1 [0xE8, 0x1A, 0xB2, 0xFF, 0xFF] (PushPre 0x1058f1 5) (callEffect (fun _ => 0x100b10) 0x1058f6)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1058f1 0x100b10 0x1058f6).toInstrSpec (call_rel32_effect_step 0x1058f1 0xffffb21a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058e8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058ec) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058f1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b10) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1058e4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1058e4 :=
  Rest.liftedBlock (rest_l1058e4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1058e4 x hx)

theorem rest_l1058f6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1058f6 bytes_l1058f6) (entryMap (live .l1058f6))
      11 0x1058f6 bytes_l1058f6 b_l1058f6 := by
  have f0 : InstrSpec 0x1058f6 [0x66, 0xF7, 0x54, 0x1C, 0x1C] (StorePre 0x1058f6 5 (fun s => AddrMode.addr (.sib 4 (some 3) 0 (.d8 0x1c)) s (0x1058f6 + BitVec.ofNat 64 5)) 2) (notMEffect 0x1058f6 5 16 (.sib 4 (some 3) 0 (.d8 0x1c)))
      [.gpr 4, .gpr 3] [] [.rip] :=
    (notMEffect16_footprint 0x1058f6 5 (.sib 4 (some 3) 0 (.d8 0x1c))).toInstrSpec (not_m16_effect_step 0x1058f6 (.sib 4 (some 3) 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1058fb [0x66, 0xF7, 0x54, 0x1C, 0x1E] (StorePre 0x1058fb 5 (fun s => AddrMode.addr (.sib 4 (some 3) 0 (.d8 0x1e)) s (0x1058fb + BitVec.ofNat 64 5)) 2) (notMEffect 0x1058fb 5 16 (.sib 4 (some 3) 0 (.d8 0x1e)))
      [.gpr 4, .gpr 3] [] [.rip] :=
    (notMEffect16_footprint 0x1058fb 5 (.sib 4 (some 3) 0 (.d8 0x1e))).toInstrSpec (not_m16_effect_step 0x1058fb (.sib 4 (some 3) 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x105900 [0x66, 0xF7, 0x54, 0x1C, 0x26] (StorePre 0x105900 5 (fun s => AddrMode.addr (.sib 4 (some 3) 0 (.d8 0x26)) s (0x105900 + BitVec.ofNat 64 5)) 2) (notMEffect 0x105900 5 16 (.sib 4 (some 3) 0 (.d8 0x26)))
      [.gpr 4, .gpr 3] [] [.rip] :=
    (notMEffect16_footprint 0x105900 5 (.sib 4 (some 3) 0 (.d8 0x26))).toInstrSpec (not_m16_effect_step 0x105900 (.sib 4 (some 3) 0 (.d8 0x26)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x105905 [0x66, 0xF7, 0x54, 0x1C, 0x28] (StorePre 0x105905 5 (fun s => AddrMode.addr (.sib 4 (some 3) 0 (.d8 0x28)) s (0x105905 + BitVec.ofNat 64 5)) 2) (notMEffect 0x105905 5 16 (.sib 4 (some 3) 0 (.d8 0x28)))
      [.gpr 4, .gpr 3] [] [.rip] :=
    (notMEffect16_footprint 0x105905 5 (.sib 4 (some 3) 0 (.d8 0x28))).toInstrSpec (not_m16_effect_step 0x105905 (.sib 4 (some 3) 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10590a [0x49, 0x83, 0xC7, 0x08] (fun s => s.RIP = 0x10590a) (addR64Imm8Effect 0x10590a 15 0x8)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10590a 15 0x8).toInstrSpec (add_r64_imm8_effect_step 0x10590a 0x49 0xc7 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10590e [0xBE, 0x78, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10590e) (movR32Imm32Effect 0x10590e 5 6 0x78)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10590e 5 6 0x78).toInstrSpec (mov_r32_imm32_effect_step 0x10590e 0xbe (by decide) 0x78) pre_rip
  have f6 : InstrSpec 0x105913 [0xB9, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105913) (movR32Imm32Effect 0x105913 5 1 0x10)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x105913 5 1 0x10).toInstrSpec (mov_r32_imm32_effect_step 0x105913 0xb9 (by decide) 0x10) pre_rip
  have f7 : InstrSpec 0x105918 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x105918) (movR64R64Effect 0x105918 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105918 7 14).toInstrSpec (mov_r64_r64_effect_step 0x105918 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10591b [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x10591b) (movR64R64Effect 0x10591b 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10591b 2 15).toInstrSpec (mov_r64_r64_effect_step 0x10591b 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10591e [0x41, 0xB8, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10591e) (movR32Imm32Effect 0x10591e 6 8 0x3)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x10591e 6 8 0x3).toInstrSpec (mov_r32_imm32_rex_effect_step 0x10591e 0x41 0xb8 (by decide) (by decide) 0x3) pre_rip
  have f10 : InstrSpec 0x105924 [0xE8, 0xE7, 0xE6, 0xFF, 0xFF] (PushPre 0x105924 5) (callEffect (fun _ => 0x104010) 0x105929)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105924 0x104010 0x105929).toInstrSpec (call_rel32_effect_step 0x105924 0xffffe6e7 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058fb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105900) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105905) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10590a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10590e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105913) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (3, 3), (4, 4), (5, 5), (6, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105918) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10591b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 61), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10591e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 61), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (8, 67), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105924) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 61), (2, 65), (3, 3), (4, 69), (5, 5), (6, 59), (7, 63), (8, 67), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104010) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l1058f6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1058f6 :=
  Rest.liftedBlock (rest_l1058f6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1058f6 x hx)

theorem rest_l105929 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105929 bytes_l105929) (entryMap (live .l105929))
      4 0x105929 bytes_l105929 b_l105929 := by
  have f0 : InstrSpec 0x105929 [0x49, 0x83, 0xC5, 0x22] (fun s => s.RIP = 0x105929) (addR64Imm8Effect 0x105929 13 0x22)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x105929 13 0x22).toInstrSpec (add_r64_imm8_effect_step 0x105929 0x49 0xc5 0x22 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10592d [0x48, 0x83, 0xC3, 0x20] (fun s => s.RIP = 0x10592d) (addR64Imm8Effect 0x10592d 3 0x20)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10592d 3 0x20).toInstrSpec (add_r64_imm8_effect_step 0x10592d 0x48 0xc3 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x105931 [0x49, 0x83, 0xC4, 0x20] (fun s => s.RIP = 0x105931) (addR64Imm8Effect 0x105931 12 0x20)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x105931 12 0x20).toInstrSpec (add_r64_imm8_effect_step 0x105931 0x49 0xc4 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10592d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 55), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105931) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (3, 55), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 57), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105935) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x105935 0xffffff36 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l105929 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105929 :=
  Rest.liftedBlock (rest_l105929 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105929 x hx)

theorem rest_l10593a_59 [Bindings] (code : CodeMap) :
    Rest (n := 2295) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 2279), (1, 2285), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2290), (8, 2287), (9, 2293), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]
      12 0x1068ef bytes_l10593a_59 b_l10593a_59 := by
  have f1180 : InstrSpec 0x1068ef [0x66, 0x44, 0x89, 0x8C, 0x24, 0xE6, 0x00, 0x00, 0x00] (StorePre 0x1068ef 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe6)) s (0x1068ef + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x1068ef 9 9 (.sib 4 none 0 (.d32 0xe6)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1068ef 9 9 (.sib 4 none 0 (.d32 0xe6))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1068ef 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0xe6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1181 : InstrSpec 0x1068f8 [0xF7, 0xD1] (fun s => s.RIP = 0x1068f8) (notR32Effect 0x1068f8 2 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR32Effect_footprint 0x1068f8 2 1).toInstrSpec (not_r32_effect_step 0x1068f8 0xd1 (by decide) (by decide)) pre_rip
  have f1182 : InstrSpec 0x1068fa [0x66, 0x89, 0x8C, 0x24, 0xE8, 0x00, 0x00, 0x00] (StorePre 0x1068fa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1068fa + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1068fa 8 1 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1068fa 8 1 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_m16_r16_effect_step 0x1068fa 1 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1183 : InstrSpec 0x106902 [0x66, 0xF7, 0x94, 0x24, 0xEC, 0x00, 0x00, 0x00] (StorePre 0x106902 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xec)) s (0x106902 + BitVec.ofNat 64 8)) 2) (notMEffect 0x106902 8 16 (.sib 4 none 0 (.d32 0xec)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x106902 8 (.sib 4 none 0 (.d32 0xec))).toInstrSpec (not_m16_effect_step 0x106902 (.sib 4 none 0 (.d32 0xec)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1184 : InstrSpec 0x10690a [0x66, 0xF7, 0x94, 0x24, 0xEE, 0x00, 0x00, 0x00] (StorePre 0x10690a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xee)) s (0x10690a + BitVec.ofNat 64 8)) 2) (notMEffect 0x10690a 8 16 (.sib 4 none 0 (.d32 0xee)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x10690a 8 (.sib 4 none 0 (.d32 0xee))).toInstrSpec (not_m16_effect_step 0x10690a (.sib 4 none 0 (.d32 0xee)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1185 : InstrSpec 0x106912 [0x66, 0xF7, 0x94, 0x24, 0xF6, 0x00, 0x00, 0x00] (StorePre 0x106912 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf6)) s (0x106912 + BitVec.ofNat 64 8)) 2) (notMEffect 0x106912 8 16 (.sib 4 none 0 (.d32 0xf6)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x106912 8 (.sib 4 none 0 (.d32 0xf6))).toInstrSpec (not_m16_effect_step 0x106912 (.sib 4 none 0 (.d32 0xf6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1186 : InstrSpec 0x10691a [0x66, 0xF7, 0x94, 0x24, 0xF8, 0x00, 0x00, 0x00] (StorePre 0x10691a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10691a + BitVec.ofNat 64 8)) 2) (notMEffect 0x10691a 8 16 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x10691a 8 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (not_m16_effect_step 0x10691a (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1187 : InstrSpec 0x106922 [0x48, 0x8D, 0x74, 0x24, 0x0C] (fun s => s.RIP = 0x106922) (leaR64Effect 0x106922 6 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x106922 6 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (lea_r64_effect_step 0x106922 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) pre_rip
  have f1188 : InstrSpec 0x106927 [0xBA, 0xF0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106927) (movR32Imm32Effect 0x106927 5 2 0xf0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x106927 5 2 0xf0).toInstrSpec (mov_r32_imm32_effect_step 0x106927 0xba (by decide) 0xf0) pre_rip
  have f1189 : InstrSpec 0x10692c [0x48, 0x8B, 0x9C, 0x24, 0x30, 0x01, 0x00, 0x00] (LoadPre 0x10692c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10692c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10692c 3 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x10692c 3 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_r64_m64_effect_step 0x10692c 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1190 : InstrSpec 0x106934 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x106934) (movR64R64Effect 0x106934 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x106934 7 3).toInstrSpec (mov_r64_r64_effect_step 0x106934 0x48 0xdf (by decide) (by decide)) pre_rip
  have f1191 : InstrSpec 0x106937 [0xFF, 0x15, 0xCB, 0xA8, 0x0F, 0x00] (GoesTo (CallMemPre 0x106937 (.rip 0xfa8cb)) (callEffect (callMemPtr 0x106937 (.rip 0xfa8cb)) (0x106937 + BitVec.ofNat 64 (callMemLen (.rip 0xfa8cb)))) 0x103f00) (callEffect (callMemPtr 0x106937 (.rip 0xfa8cb)) (0x106937 + BitVec.ofNat 64 (callMemLen (.rip 0xfa8cb))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x106937 (.rip 0xfa8cb)).toInstrSpec (call_m64_effect_step 0x106937 (.rip 0xfa8cb) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 2295) (RestInside.exec (n := 2295) (ρ' := [(0, 2279), (1, 2285), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2290), (8, 2287), (9, 2293), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068f8) f1180 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2296) (RestInside.out (n := 2296) f1181 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2297) (ρ' := [(0, 2279), (1, 2296), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2290), (8, 2287), (9, 2293), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068fa) f1181 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2298) (RestInside.exec (n := 2298) (ρ' := [(0, 2279), (1, 2296), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2290), (8, 2287), (9, 2293), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106902) f1182 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2299) (RestInside.exec (n := 2299) (ρ' := [(0, 2279), (1, 2296), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2290), (8, 2287), (9, 2293), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10690a) f1183 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2300) (RestInside.exec (n := 2300) (ρ' := [(0, 2279), (1, 2296), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2290), (8, 2287), (9, 2293), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106912) f1184 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2301) (RestInside.exec (n := 2301) (ρ' := [(0, 2279), (1, 2296), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2290), (8, 2287), (9, 2293), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10691a) f1185 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2302) (RestInside.exec (n := 2302) (ρ' := [(0, 2279), (1, 2296), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2290), (8, 2287), (9, 2293), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106922) f1186 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2303) (RestInside.out (n := 2303) f1187 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2304) (ρ' := [(0, 2279), (1, 2296), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2303), (7, 2290), (8, 2287), (9, 2293), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106927) f1187 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2305) (RestInside.out (n := 2305) f1188 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2306) (ρ' := [(0, 2279), (1, 2296), (2, 2305), (3, 2257), (4, 4), (5, 2254), (6, 2303), (7, 2290), (8, 2287), (9, 2293), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10692c) f1188 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2307) (RestInside.out (n := 2307) f1189 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2308) (ρ' := [(0, 2279), (1, 2296), (2, 2305), (3, 2307), (4, 4), (5, 2254), (6, 2303), (7, 2290), (8, 2287), (9, 2293), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106934) f1189 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2309) (RestInside.out (n := 2309) f1190 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2310) (ρ' := [(0, 2279), (1, 2296), (2, 2305), (3, 2307), (4, 4), (5, 2254), (6, 2303), (7, 2309), (8, 2287), (9, 2293), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106937) f1190 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2311) (RestInside.out (n := 2311) f1191 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2312) (ρ' := [(0, 2279), (1, 2296), (2, 2305), (3, 2307), (4, 2311), (5, 2254), (6, 2303), (7, 2309), (8, 2287), (9, 2293), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f1191 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 2313) (by decide) (by decide) rfl rfl

theorem rest_l10593a_58 [Bindings] (code : CodeMap) :
    Rest (n := 2265) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 2247), (1, 2223), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]
      32 0x106883 bytes_l10593a_58 b_l10593a_58 := by
  have f1160 : InstrSpec 0x106883 [0x66, 0x44, 0x89, 0x94, 0x24, 0xBC, 0x00, 0x00, 0x00] (StorePre 0x106883 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbc)) s (0x106883 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x106883 9 10 (.sib 4 none 0 (.d32 0xbc)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106883 9 10 (.sib 4 none 0 (.d32 0xbc))).toInstrSpec (mov_m16_r16_rex_effect_step 0x106883 0x44 (by decide) 2 (.sib 4 none 0 (.d32 0xbc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1161 : InstrSpec 0x10688c [0x66, 0xF7, 0x94, 0x24, 0xBE, 0x00, 0x00, 0x00] (StorePre 0x10688c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbe)) s (0x10688c + BitVec.ofNat 64 8)) 2) (notMEffect 0x10688c 8 16 (.sib 4 none 0 (.d32 0xbe)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x10688c 8 (.sib 4 none 0 (.d32 0xbe))).toInstrSpec (not_m16_effect_step 0x10688c (.sib 4 none 0 (.d32 0xbe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1162 : InstrSpec 0x106894 [0x89, 0xC1] (fun s => s.RIP = 0x106894) (movR32R32Effect 0x106894 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106894 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x106894 0xc1 (by decide)) pre_rip
  have f1163 : InstrSpec 0x106896 [0x66, 0xF7, 0x94, 0x24, 0xC6, 0x00, 0x00, 0x00] (StorePre 0x106896 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc6)) s (0x106896 + BitVec.ofNat 64 8)) 2) (notMEffect 0x106896 8 16 (.sib 4 none 0 (.d32 0xc6)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x106896 8 (.sib 4 none 0 (.d32 0xc6))).toInstrSpec (not_m16_effect_step 0x106896 (.sib 4 none 0 (.d32 0xc6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1164 : InstrSpec 0x10689e [0xD1, 0xE9] (fun s => s.RIP = 0x10689e) (shrR32Effect 0x10689e 2 1 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10689e 2 1 1).toInstrSpec (shr_r32_one_effect_step 0x10689e 0xe9 (by decide) (by decide)) pre_rip
  have f1165 : InstrSpec 0x1068a0 [0x66, 0xF7, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x1068a0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1068a0 + BitVec.ofNat 64 8)) 2) (notMEffect 0x1068a0 8 16 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x1068a0 8 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (not_m16_effect_step 0x1068a0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1166 : InstrSpec 0x1068a8 [0x31, 0xC1] (fun s => s.RIP = 0x1068a8) (xorR32R32Effect 0x1068a8 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1068a8 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1068a8 0xc1 (by decide)) pre_rip
  have f1167 : InstrSpec 0x1068aa [0x66, 0xF7, 0x94, 0x24, 0xCC, 0x00, 0x00, 0x00] (StorePre 0x1068aa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc)) s (0x1068aa + BitVec.ofNat 64 8)) 2) (notMEffect 0x1068aa 8 16 (.sib 4 none 0 (.d32 0xcc)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x1068aa 8 (.sib 4 none 0 (.d32 0xcc))).toInstrSpec (not_m16_effect_step 0x1068aa (.sib 4 none 0 (.d32 0xcc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1168 : InstrSpec 0x1068b2 [0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1068b2) (andR32Imm32Effect 0x1068b2 6 1 0x5050)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1068b2 6 1 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x1068b2 0xe1 0x5050 (by decide) (by decide)) pre_rip
  have f1169 : InstrSpec 0x1068b8 [0x66, 0xF7, 0x94, 0x24, 0xCE, 0x00, 0x00, 0x00] (StorePre 0x1068b8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xce)) s (0x1068b8 + BitVec.ofNat 64 8)) 2) (notMEffect 0x1068b8 8 16 (.sib 4 none 0 (.d32 0xce)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x1068b8 8 (.sib 4 none 0 (.d32 0xce))).toInstrSpec (not_m16_effect_step 0x1068b8 (.sib 4 none 0 (.d32 0xce)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1170 : InstrSpec 0x1068c0 [0x31, 0xC8] (fun s => s.RIP = 0x1068c0) (xorR32R32Effect 0x1068c0 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1068c0 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1068c0 0xc8 (by decide)) pre_rip
  have f1171 : InstrSpec 0x1068c2 [0x66, 0xF7, 0x94, 0x24, 0xD6, 0x00, 0x00, 0x00] (StorePre 0x1068c2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd6)) s (0x1068c2 + BitVec.ofNat 64 8)) 2) (notMEffect 0x1068c2 8 16 (.sib 4 none 0 (.d32 0xd6)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x1068c2 8 (.sib 4 none 0 (.d32 0xd6))).toInstrSpec (not_m16_effect_step 0x1068c2 (.sib 4 none 0 (.d32 0xd6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1172 : InstrSpec 0x1068ca [0x01, 0xC9] (fun s => s.RIP = 0x1068ca) (addR32R32Effect 0x1068ca 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1068ca 2 1 1).toInstrSpec (add_r32_r32_effect_step 0x1068ca 0xc9 (by decide)) pre_rip
  have f1173 : InstrSpec 0x1068cc [0x66, 0xF7, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x1068cc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1068cc + BitVec.ofNat 64 8)) 2) (notMEffect 0x1068cc 8 16 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x1068cc 8 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (not_m16_effect_step 0x1068cc (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1174 : InstrSpec 0x1068d4 [0x31, 0xC1] (fun s => s.RIP = 0x1068d4) (xorR32R32Effect 0x1068d4 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1068d4 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1068d4 0xc1 (by decide)) pre_rip
  have f1175 : InstrSpec 0x1068d6 [0x41, 0xF7, 0xD0] (fun s => s.RIP = 0x1068d6) (notR32Effect 0x1068d6 3 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (notR32Effect_footprint 0x1068d6 3 8).toInstrSpec (not_r32_rex_effect_step 0x1068d6 0x41 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f1176 : InstrSpec 0x1068d9 [0x66, 0x44, 0x89, 0x84, 0x24, 0xDC, 0x00, 0x00, 0x00] (StorePre 0x1068d9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xdc)) s (0x1068d9 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x1068d9 9 8 (.sib 4 none 0 (.d32 0xdc)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1068d9 9 8 (.sib 4 none 0 (.d32 0xdc))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1068d9 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0xdc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1177 : InstrSpec 0x1068e2 [0xF7, 0xD7] (fun s => s.RIP = 0x1068e2) (notR32Effect 0x1068e2 2 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (notR32Effect_footprint 0x1068e2 2 7).toInstrSpec (not_r32_effect_step 0x1068e2 0xd7 (by decide) (by decide)) pre_rip
  have f1178 : InstrSpec 0x1068e4 [0x66, 0x89, 0xBC, 0x24, 0xDE, 0x00, 0x00, 0x00] (StorePre 0x1068e4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xde)) s (0x1068e4 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1068e4 8 7 (.sib 4 none 0 (.d32 0xde)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1068e4 8 7 (.sib 4 none 0 (.d32 0xde))).toInstrSpec (mov_m16_r16_effect_step 0x1068e4 7 (.sib 4 none 0 (.d32 0xde)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1179 : InstrSpec 0x1068ec [0x41, 0xF7, 0xD1] (fun s => s.RIP = 0x1068ec) (notR32Effect 0x1068ec 3 9)
      [.gpr 9] [] [.reg 9, .rip] :=
    (notR32Effect_footprint 0x1068ec 3 9).toInstrSpec (not_r32_rex_effect_step 0x1068ec 0x41 0xd1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 2265) (RestInside.exec (n := 2265) (ρ' := [(0, 2247), (1, 2223), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10688c) f1160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2266) (RestInside.exec (n := 2266) (ρ' := [(0, 2247), (1, 2223), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106894) f1161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2267) (RestInside.out (n := 2267) f1162 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2268) (ρ' := [(0, 2247), (1, 2267), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106896) f1162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2269) (RestInside.exec (n := 2269) (ρ' := [(0, 2247), (1, 2267), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10689e) f1163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2270) (RestInside.out (n := 2270) f1164 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2271) (ρ' := [(0, 2247), (1, 2270), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068a0) f1164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2272) (RestInside.exec (n := 2272) (ρ' := [(0, 2247), (1, 2270), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068a8) f1165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2273) (RestInside.out (n := 2273) f1166 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2274) (ρ' := [(0, 2247), (1, 2273), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068aa) f1166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2275) (RestInside.exec (n := 2275) (ρ' := [(0, 2247), (1, 2273), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068b2) f1167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2276) (RestInside.out (n := 2276) f1168 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2277) (ρ' := [(0, 2247), (1, 2276), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068b8) f1168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2278) (RestInside.exec (n := 2278) (ρ' := [(0, 2247), (1, 2276), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068c0) f1169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2279) (RestInside.out (n := 2279) f1170 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2280) (ρ' := [(0, 2279), (1, 2276), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068c2) f1170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2281) (RestInside.exec (n := 2281) (ρ' := [(0, 2279), (1, 2276), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068ca) f1171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2282) (RestInside.out (n := 2282) f1172 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2283) (ρ' := [(0, 2279), (1, 2282), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068cc) f1172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2284) (RestInside.exec (n := 2284) (ρ' := [(0, 2279), (1, 2282), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068d4) f1173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2285) (RestInside.out (n := 2285) f1174 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2286) (ρ' := [(0, 2279), (1, 2285), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068d6) f1174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2287) (RestInside.out (n := 2287) f1175 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2288) (ρ' := [(0, 2279), (1, 2285), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 2287), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068d9) f1175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2289) (RestInside.exec (n := 2289) (ρ' := [(0, 2279), (1, 2285), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 2287), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068e2) f1176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2290) (RestInside.out (n := 2290) f1177 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2291) (ρ' := [(0, 2279), (1, 2285), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2290), (8, 2287), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068e4) f1177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2292) (RestInside.exec (n := 2292) (ρ' := [(0, 2279), (1, 2285), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2290), (8, 2287), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068ec) f1178 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2293) (RestInside.out (n := 2293) f1179 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2294) (ρ' := [(0, 2279), (1, 2285), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2290), (8, 2287), (9, 2293), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1068ef) f1179 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_59 code

theorem rest_l10593a_57 [Bindings] (code : CodeMap) :
    Rest (n := 2233) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 2198), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]
      52 0x106820 bytes_l10593a_57 b_l10593a_57 := by
  have f1140 : InstrSpec 0x106820 [0x66, 0x44, 0x89, 0xA4, 0x24, 0x9C, 0x00, 0x00, 0x00] (StorePre 0x106820 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x106820 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x106820 9 12 (.sib 4 none 0 (.d32 0x9c)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106820 9 12 (.sib 4 none 0 (.d32 0x9c))).toInstrSpec (mov_m16_r16_rex_effect_step 0x106820 0x44 (by decide) 4 (.sib 4 none 0 (.d32 0x9c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1141 : InstrSpec 0x106829 [0x89, 0xF0] (fun s => s.RIP = 0x106829) (movR32R32Effect 0x106829 2 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106829 2 0 6).toInstrSpec (mov_r32_r32_effect_step 0x106829 0xf0 (by decide)) pre_rip
  have f1142 : InstrSpec 0x10682b [0xC1, 0xE8, 0x02] (fun s => s.RIP = 0x10682b) (shrR32Effect 0x10682b 3 0 2)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x10682b 3 0 2).toInstrSpec (shr_r32_imm8_effect_step 0x10682b 0xe8 0x2 (by decide) (by decide)) pre_rip
  have f1143 : InstrSpec 0x10682e [0x31, 0xF0] (fun s => s.RIP = 0x10682e) (xorR32R32Effect 0x10682e 2 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10682e 2 0 6).toInstrSpec (xor_r32_r32_effect_step 0x10682e 0xf0 (by decide)) pre_rip
  have f1144 : InstrSpec 0x106830 [0x25, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x106830) (andEaxImm32Effect 0x106830 0x1320)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106830 0x1320).toInstrSpec (and_eax_imm32_effect_step 0x106830 0x1320) pre_rip
  have f1145 : InstrSpec 0x106835 [0x31, 0xC6] (fun s => s.RIP = 0x106835) (xorR32R32Effect 0x106835 2 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106835 2 6 0).toInstrSpec (xor_r32_r32_effect_step 0x106835 0xc6 (by decide)) pre_rip
  have f1146 : InstrSpec 0x106837 [0xC1, 0xE0, 0x02] (fun s => s.RIP = 0x106837) (shlR32Effect 0x106837 3 0 2)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x106837 3 0 2).toInstrSpec (shl_r32_imm8_effect_step 0x106837 0xe0 0x2 (by decide) (by decide)) pre_rip
  have f1147 : InstrSpec 0x10683a [0x66, 0xF7, 0x94, 0x24, 0x9E, 0x00, 0x00, 0x00] (StorePre 0x10683a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9e)) s (0x10683a + BitVec.ofNat 64 8)) 2) (notMEffect 0x10683a 8 16 (.sib 4 none 0 (.d32 0x9e)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x10683a 8 (.sib 4 none 0 (.d32 0x9e))).toInstrSpec (not_m16_effect_step 0x10683a (.sib 4 none 0 (.d32 0x9e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1148 : InstrSpec 0x106842 [0x31, 0xF0] (fun s => s.RIP = 0x106842) (xorR32R32Effect 0x106842 2 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106842 2 0 6).toInstrSpec (xor_r32_r32_effect_step 0x106842 0xf0 (by decide)) pre_rip
  have f1149 : InstrSpec 0x106844 [0x66, 0xF7, 0x94, 0x24, 0xA6, 0x00, 0x00, 0x00] (StorePre 0x106844 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa6)) s (0x106844 + BitVec.ofNat 64 8)) 2) (notMEffect 0x106844 8 16 (.sib 4 none 0 (.d32 0xa6)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x106844 8 (.sib 4 none 0 (.d32 0xa6))).toInstrSpec (not_m16_effect_step 0x106844 (.sib 4 none 0 (.d32 0xa6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1150 : InstrSpec 0x10684c [0x66, 0xF7, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x10684c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10684c + BitVec.ofNat 64 8)) 2) (notMEffect 0x10684c 8 16 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x10684c 8 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (not_m16_effect_step 0x10684c (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1151 : InstrSpec 0x106854 [0x41, 0xF7, 0xD5] (fun s => s.RIP = 0x106854) (notR32Effect 0x106854 3 13)
      [.gpr 13] [] [.reg 13, .rip] :=
    (notR32Effect_footprint 0x106854 3 13).toInstrSpec (not_r32_rex_effect_step 0x106854 0x41 0xd5 (by decide) (by decide) (by decide)) pre_rip
  have f1152 : InstrSpec 0x106857 [0x66, 0x44, 0x89, 0xAC, 0x24, 0xAC, 0x00, 0x00, 0x00] (StorePre 0x106857 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xac)) s (0x106857 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x106857 9 13 (.sib 4 none 0 (.d32 0xac)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106857 9 13 (.sib 4 none 0 (.d32 0xac))).toInstrSpec (mov_m16_r16_rex_effect_step 0x106857 0x44 (by decide) 5 (.sib 4 none 0 (.d32 0xac)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1153 : InstrSpec 0x106860 [0xF7, 0xD5] (fun s => s.RIP = 0x106860) (notR32Effect 0x106860 2 5)
      [.gpr 5] [] [.reg 5, .rip] :=
    (notR32Effect_footprint 0x106860 2 5).toInstrSpec (not_r32_effect_step 0x106860 0xd5 (by decide) (by decide)) pre_rip
  have f1154 : InstrSpec 0x106862 [0x66, 0x89, 0xAC, 0x24, 0xAE, 0x00, 0x00, 0x00] (StorePre 0x106862 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xae)) s (0x106862 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106862 8 5 (.sib 4 none 0 (.d32 0xae)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106862 8 5 (.sib 4 none 0 (.d32 0xae))).toInstrSpec (mov_m16_r16_effect_step 0x106862 5 (.sib 4 none 0 (.d32 0xae)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1155 : InstrSpec 0x10686a [0xF7, 0xD3] (fun s => s.RIP = 0x10686a) (notR32Effect 0x10686a 2 3)
      [.gpr 3] [] [.reg 3, .rip] :=
    (notR32Effect_footprint 0x10686a 2 3).toInstrSpec (not_r32_effect_step 0x10686a 0xd3 (by decide) (by decide)) pre_rip
  have f1156 : InstrSpec 0x10686c [0x66, 0x89, 0x9C, 0x24, 0xB6, 0x00, 0x00, 0x00] (StorePre 0x10686c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb6)) s (0x10686c + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x10686c 8 3 (.sib 4 none 0 (.d32 0xb6)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10686c 8 3 (.sib 4 none 0 (.d32 0xb6))).toInstrSpec (mov_m16_r16_effect_step 0x10686c 3 (.sib 4 none 0 (.d32 0xb6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1157 : InstrSpec 0x106874 [0x41, 0xF7, 0xD3] (fun s => s.RIP = 0x106874) (notR32Effect 0x106874 3 11)
      [.gpr 11] [] [.reg 11, .rip] :=
    (notR32Effect_footprint 0x106874 3 11).toInstrSpec (not_r32_rex_effect_step 0x106874 0x41 0xd3 (by decide) (by decide) (by decide)) pre_rip
  have f1158 : InstrSpec 0x106877 [0x66, 0x44, 0x89, 0x9C, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x106877 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x106877 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x106877 9 11 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106877 9 11 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m16_r16_rex_effect_step 0x106877 0x44 (by decide) 3 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1159 : InstrSpec 0x106880 [0x41, 0xF7, 0xD2] (fun s => s.RIP = 0x106880) (notR32Effect 0x106880 3 10)
      [.gpr 10] [] [.reg 10, .rip] :=
    (notR32Effect_footprint 0x106880 3 10).toInstrSpec (not_r32_rex_effect_step 0x106880 0x41 0xd2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 2233) (RestInside.exec (n := 2233) (ρ' := [(0, 2198), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106829) f1140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2234) (RestInside.out (n := 2234) f1141 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2235) (ρ' := [(0, 2234), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10682b) f1141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2236) (RestInside.out (n := 2236) f1142 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2237) (ρ' := [(0, 2236), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10682e) f1142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2238) (RestInside.out (n := 2238) f1143 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2239) (ρ' := [(0, 2238), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106830) f1143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2240) (RestInside.out (n := 2240) f1144 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2241) (ρ' := [(0, 2240), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106835) f1144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2242) (RestInside.out (n := 2242) f1145 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2243) (ρ' := [(0, 2240), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106837) f1145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2244) (RestInside.out (n := 2244) f1146 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2245) (ρ' := [(0, 2244), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10683a) f1146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2246) (RestInside.exec (n := 2246) (ρ' := [(0, 2244), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106842) f1147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2247) (RestInside.out (n := 2247) f1148 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2248) (ρ' := [(0, 2247), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106844) f1148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2249) (RestInside.exec (n := 2249) (ρ' := [(0, 2247), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10684c) f1149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2250) (RestInside.exec (n := 2250) (ρ' := [(0, 2247), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106854) f1150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2251) (RestInside.out (n := 2251) f1151 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2252) (ρ' := [(0, 2247), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106857) f1151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2253) (RestInside.exec (n := 2253) (ρ' := [(0, 2247), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106860) f1152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2254) (RestInside.out (n := 2254) f1153 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2255) (ρ' := [(0, 2247), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106862) f1153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2256) (RestInside.exec (n := 2256) (ρ' := [(0, 2247), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10686a) f1154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2257) (RestInside.out (n := 2257) f1155 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2258) (ρ' := [(0, 2247), (1, 2223), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10686c) f1155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2259) (RestInside.exec (n := 2259) (ρ' := [(0, 2247), (1, 2223), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106874) f1156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2260) (RestInside.out (n := 2260) f1157 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2261) (ρ' := [(0, 2247), (1, 2223), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106877) f1157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2262) (RestInside.exec (n := 2262) (ρ' := [(0, 2247), (1, 2223), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106880) f1158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2263) (RestInside.out (n := 2263) f1159 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2264) (ρ' := [(0, 2247), (1, 2223), (2, 2182), (3, 2257), (4, 4), (5, 2254), (6, 2242), (7, 2167), (8, 1969), (9, 2229), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106883) f1159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_58 code

theorem rest_l10593a_56 [Bindings] (code : CodeMap) :
    Rest (n := 2203) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2201), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      72 0x1067b7 bytes_l10593a_56 b_l10593a_56 := by
  have f1120 : InstrSpec 0x1067b7 [0x66, 0x44, 0x89, 0x4C, 0x24, 0x76] (StorePre 0x1067b7 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x1067b7 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1067b7 6 9 (.sib 4 none 0 (.d8 0x76)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1067b7 6 9 (.sib 4 none 0 (.d8 0x76))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1067b7 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x76)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1121 : InstrSpec 0x1067bd [0x41, 0xF7, 0xD6] (fun s => s.RIP = 0x1067bd) (notR32Effect 0x1067bd 3 14)
      [.gpr 14] [] [.reg 14, .rip] :=
    (notR32Effect_footprint 0x1067bd 3 14).toInstrSpec (not_r32_rex_effect_step 0x1067bd 0x41 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f1122 : InstrSpec 0x1067c0 [0x66, 0x44, 0x89, 0x74, 0x24, 0x78] (StorePre 0x1067c0 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1067c0 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1067c0 6 14 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1067c0 6 14 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1067c0 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1123 : InstrSpec 0x1067c6 [0x41, 0xF7, 0xD7] (fun s => s.RIP = 0x1067c6) (notR32Effect 0x1067c6 3 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (notR32Effect_footprint 0x1067c6 3 15).toInstrSpec (not_r32_rex_effect_step 0x1067c6 0x41 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f1124 : InstrSpec 0x1067c9 [0x66, 0x44, 0x89, 0x7C, 0x24, 0x7C] (StorePre 0x1067c9 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x1067c9 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1067c9 6 15 (.sib 4 none 0 (.d8 0x7c)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1067c9 6 15 (.sib 4 none 0 (.d8 0x7c))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1067c9 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x7c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1125 : InstrSpec 0x1067cf [0x66, 0xF7, 0x54, 0x24, 0x7E] (StorePre 0x1067cf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7e)) s (0x1067cf + BitVec.ofNat 64 5)) 2) (notMEffect 0x1067cf 5 16 (.sib 4 none 0 (.d8 0x7e)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x1067cf 5 (.sib 4 none 0 (.d8 0x7e))).toInstrSpec (not_m16_effect_step 0x1067cf (.sib 4 none 0 (.d8 0x7e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1126 : InstrSpec 0x1067d4 [0x41, 0x89, 0xC9] (fun s => s.RIP = 0x1067d4) (movR32R32Effect 0x1067d4 3 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x1067d4 3 9 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x1067d4 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f1127 : InstrSpec 0x1067d7 [0x66, 0xF7, 0x94, 0x24, 0x86, 0x00, 0x00, 0x00] (StorePre 0x1067d7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x86)) s (0x1067d7 + BitVec.ofNat 64 8)) 2) (notMEffect 0x1067d7 8 16 (.sib 4 none 0 (.d32 0x86)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x1067d7 8 (.sib 4 none 0 (.d32 0x86))).toInstrSpec (not_m16_effect_step 0x1067d7 (.sib 4 none 0 (.d32 0x86)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1128 : InstrSpec 0x1067df [0x41, 0xD1, 0xE9] (fun s => s.RIP = 0x1067df) (shrR32Effect 0x1067df 3 9 1)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x1067df 3 9 1).toInstrSpec (shr_r32_one_rex_effect_step 0x1067df 0x41 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f1129 : InstrSpec 0x1067e2 [0x66, 0xF7, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1067e2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1067e2 + BitVec.ofNat 64 8)) 2) (notMEffect 0x1067e2 8 16 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x1067e2 8 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (not_m16_effect_step 0x1067e2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1130 : InstrSpec 0x1067ea [0x41, 0x31, 0xC9] (fun s => s.RIP = 0x1067ea) (xorR32R32Effect 0x1067ea 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1067ea 3 9 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x1067ea 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f1131 : InstrSpec 0x1067ed [0x66, 0xF7, 0x94, 0x24, 0x8C, 0x00, 0x00, 0x00] (StorePre 0x1067ed 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x1067ed + BitVec.ofNat 64 8)) 2) (notMEffect 0x1067ed 8 16 (.sib 4 none 0 (.d32 0x8c)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x1067ed 8 (.sib 4 none 0 (.d32 0x8c))).toInstrSpec (not_m16_effect_step 0x1067ed (.sib 4 none 0 (.d32 0x8c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1132 : InstrSpec 0x1067f5 [0x41, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1067f5) (andR32Imm32Effect 0x1067f5 7 9 0x5050)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1067f5 7 9 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x1067f5 0x41 0xe1 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f1133 : InstrSpec 0x1067fc [0x66, 0xF7, 0x94, 0x24, 0x8E, 0x00, 0x00, 0x00] (StorePre 0x1067fc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8e)) s (0x1067fc + BitVec.ofNat 64 8)) 2) (notMEffect 0x1067fc 8 16 (.sib 4 none 0 (.d32 0x8e)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x1067fc 8 (.sib 4 none 0 (.d32 0x8e))).toInstrSpec (not_m16_effect_step 0x1067fc (.sib 4 none 0 (.d32 0x8e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1134 : InstrSpec 0x106804 [0x44, 0x31, 0xC9] (fun s => s.RIP = 0x106804) (xorR32R32Effect 0x106804 3 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106804 3 1 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x106804 0x44 0xc9 (by decide) (by decide)) pre_rip
  have f1135 : InstrSpec 0x106807 [0x66, 0xF7, 0x94, 0x24, 0x96, 0x00, 0x00, 0x00] (StorePre 0x106807 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x96)) s (0x106807 + BitVec.ofNat 64 8)) 2) (notMEffect 0x106807 8 16 (.sib 4 none 0 (.d32 0x96)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x106807 8 (.sib 4 none 0 (.d32 0x96))).toInstrSpec (not_m16_effect_step 0x106807 (.sib 4 none 0 (.d32 0x96)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1136 : InstrSpec 0x10680f [0x45, 0x01, 0xC9] (fun s => s.RIP = 0x10680f) (addR32R32Effect 0x10680f 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10680f 3 9 9).toInstrSpec (add_r32_r32_rex_effect_step 0x10680f 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f1137 : InstrSpec 0x106812 [0x66, 0xF7, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x106812 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x106812 + BitVec.ofNat 64 8)) 2) (notMEffect 0x106812 8 16 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x106812 8 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (not_m16_effect_step 0x106812 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1138 : InstrSpec 0x10681a [0x41, 0x31, 0xC9] (fun s => s.RIP = 0x10681a) (xorR32R32Effect 0x10681a 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10681a 3 9 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x10681a 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f1139 : InstrSpec 0x10681d [0x41, 0xF7, 0xD4] (fun s => s.RIP = 0x10681d) (notR32Effect 0x10681d 3 12)
      [.gpr 12] [] [.reg 12, .rip] :=
    (notR32Effect_footprint 0x10681d 3 12).toInstrSpec (not_r32_rex_effect_step 0x10681d 0x41 0xd4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 2203) (RestInside.exec (n := 2203) (ρ' := [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2201), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067bd) f1120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2204) (RestInside.out (n := 2204) f1121 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2205) (ρ' := [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2201), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067c0) f1121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2206) (RestInside.exec (n := 2206) (ρ' := [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2201), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067c6) f1122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2207) (RestInside.out (n := 2207) f1123 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2208) (ρ' := [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2201), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067c9) f1123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2209) (RestInside.exec (n := 2209) (ρ' := [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2201), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067cf) f1124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2210) (RestInside.exec (n := 2210) (ρ' := [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2201), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067d4) f1125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2211) (RestInside.out (n := 2211) f1126 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2212) (ρ' := [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2211), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067d7) f1126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2213) (RestInside.exec (n := 2213) (ρ' := [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2211), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067df) f1127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2214) (RestInside.out (n := 2214) f1128 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2215) (ρ' := [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2214), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067e2) f1128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2216) (RestInside.exec (n := 2216) (ρ' := [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2214), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067ea) f1129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2217) (RestInside.out (n := 2217) f1130 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2218) (ρ' := [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2217), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067ed) f1130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2219) (RestInside.exec (n := 2219) (ρ' := [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2217), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067f5) f1131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2220) (RestInside.out (n := 2220) f1132 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2221) (ρ' := [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2220), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067fc) f1132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2222) (RestInside.exec (n := 2222) (ρ' := [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2220), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106804) f1133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2223) (RestInside.out (n := 2223) f1134 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2224) (ρ' := [(0, 2198), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2220), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106807) f1134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2225) (RestInside.exec (n := 2225) (ρ' := [(0, 2198), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2220), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10680f) f1135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2226) (RestInside.out (n := 2226) f1136 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2227) (ρ' := [(0, 2198), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2226), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106812) f1136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2228) (RestInside.exec (n := 2228) (ρ' := [(0, 2198), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2226), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10681a) f1137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2229) (RestInside.out (n := 2229) f1138 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2230) (ρ' := [(0, 2198), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10681d) f1138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2231) (RestInside.out (n := 2231) f1139 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2232) (ρ' := [(0, 2198), (1, 2223), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2229), (10, 1722), (11, 1675), (12, 2231), (13, 1576), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106820) f1139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_57 code

theorem rest_l10593a_55 [Bindings] (code : CodeMap) :
    Rest (n := 2169) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 2145), (1, 2161), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      92 0x106767 bytes_l10593a_55 b_l10593a_55 := by
  have f1100 : InstrSpec 0x106767 [0x8B, 0x84, 0x24, 0x04, 0x01, 0x00, 0x00] (LoadPre 0x106767 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x104)) s (0x106767 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x106767 0 (.sib 4 none 0 (.d32 0x104)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x106767 0 (.sib 4 none 0 (.d32 0x104))).toInstrSpec (mov_r32_m32_low_effect_step 0x106767 0 (.sib 4 none 0 (.d32 0x104)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1101 : InstrSpec 0x10676e [0xF7, 0xD0] (fun s => s.RIP = 0x10676e) (notR32Effect 0x10676e 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR32Effect_footprint 0x10676e 2 0).toInstrSpec (not_r32_effect_step 0x10676e 0xd0 (by decide) (by decide)) pre_rip
  have f1102 : InstrSpec 0x106770 [0x66, 0x89, 0x44, 0x24, 0x5C] (StorePre 0x106770 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x106770 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106770 5 0 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106770 5 0 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (mov_m16_r16_effect_step 0x106770 0 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1103 : InstrSpec 0x106775 [0x89, 0xD1] (fun s => s.RIP = 0x106775) (movR32R32Effect 0x106775 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106775 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x106775 0xd1 (by decide)) pre_rip
  have f1104 : InstrSpec 0x106777 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x106777) (shrR32Effect 0x106777 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x106777 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x106777 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f1105 : InstrSpec 0x10677a [0x31, 0xD1] (fun s => s.RIP = 0x10677a) (xorR32R32Effect 0x10677a 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10677a 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x10677a 0xd1 (by decide)) pre_rip
  have f1106 : InstrSpec 0x10677c [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x10677c) (andR32Imm32Effect 0x10677c 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10677c 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x10677c 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f1107 : InstrSpec 0x106782 [0x31, 0xCA] (fun s => s.RIP = 0x106782) (xorR32R32Effect 0x106782 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106782 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x106782 0xca (by decide)) pre_rip
  have f1108 : InstrSpec 0x106784 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x106784) (shlR32Effect 0x106784 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x106784 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x106784 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f1109 : InstrSpec 0x106787 [0x66, 0xF7, 0x54, 0x24, 0x5E] (StorePre 0x106787 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x106787 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106787 5 16 (.sib 4 none 0 (.d8 0x5e)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x106787 5 (.sib 4 none 0 (.d8 0x5e))).toInstrSpec (not_m16_effect_step 0x106787 (.sib 4 none 0 (.d8 0x5e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1110 : InstrSpec 0x10678c [0x31, 0xD1] (fun s => s.RIP = 0x10678c) (xorR32R32Effect 0x10678c 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10678c 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x10678c 0xd1 (by decide)) pre_rip
  have f1111 : InstrSpec 0x10678e [0x66, 0xF7, 0x54, 0x24, 0x66] (StorePre 0x10678e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x10678e + BitVec.ofNat 64 5)) 2) (notMEffect 0x10678e 5 16 (.sib 4 none 0 (.d8 0x66)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x10678e 5 (.sib 4 none 0 (.d8 0x66))).toInstrSpec (not_m16_effect_step 0x10678e (.sib 4 none 0 (.d8 0x66)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1112 : InstrSpec 0x106793 [0x66, 0xF7, 0x54, 0x24, 0x68] (StorePre 0x106793 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x106793 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106793 5 16 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x106793 5 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (not_m16_effect_step 0x106793 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1113 : InstrSpec 0x106798 [0x8B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00] (LoadPre 0x106798 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x106798 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x106798 0 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x106798 0 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_r32_m32_low_effect_step 0x106798 0 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1114 : InstrSpec 0x10679f [0xF7, 0xD0] (fun s => s.RIP = 0x10679f) (notR32Effect 0x10679f 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR32Effect_footprint 0x10679f 2 0).toInstrSpec (not_r32_effect_step 0x10679f 0xd0 (by decide) (by decide)) pre_rip
  have f1115 : InstrSpec 0x1067a1 [0x66, 0x89, 0x44, 0x24, 0x6C] (StorePre 0x1067a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x1067a1 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1067a1 5 0 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1067a1 5 0 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (mov_m16_r16_effect_step 0x1067a1 0 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1116 : InstrSpec 0x1067a6 [0x8B, 0x84, 0x24, 0xFC, 0x00, 0x00, 0x00] (LoadPre 0x1067a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xfc)) s (0x1067a6 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1067a6 0 (.sib 4 none 0 (.d32 0xfc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1067a6 0 (.sib 4 none 0 (.d32 0xfc))).toInstrSpec (mov_r32_m32_low_effect_step 0x1067a6 0 (.sib 4 none 0 (.d32 0xfc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1117 : InstrSpec 0x1067ad [0xF7, 0xD0] (fun s => s.RIP = 0x1067ad) (notR32Effect 0x1067ad 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR32Effect_footprint 0x1067ad 2 0).toInstrSpec (not_r32_effect_step 0x1067ad 0xd0 (by decide) (by decide)) pre_rip
  have f1118 : InstrSpec 0x1067af [0x66, 0x89, 0x44, 0x24, 0x6E] (StorePre 0x1067af 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6e)) s (0x1067af + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1067af 5 0 (.sib 4 none 0 (.d8 0x6e)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1067af 5 0 (.sib 4 none 0 (.d8 0x6e))).toInstrSpec (mov_m16_r16_effect_step 0x1067af 0 (.sib 4 none 0 (.d8 0x6e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1119 : InstrSpec 0x1067b4 [0x41, 0xF7, 0xD1] (fun s => s.RIP = 0x1067b4) (notR32Effect 0x1067b4 3 9)
      [.gpr 9] [] [.reg 9, .rip] :=
    (notR32Effect_footprint 0x1067b4 3 9).toInstrSpec (not_r32_rex_effect_step 0x1067b4 0x41 0xd1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 2169) (RestInside.out (n := 2169) f1100 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2170) (ρ' := [(0, 2169), (1, 2161), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10676e) f1100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2171) (RestInside.out (n := 2171) f1101 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2172) (ρ' := [(0, 2171), (1, 2161), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106770) f1101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2173) (RestInside.exec (n := 2173) (ρ' := [(0, 2171), (1, 2161), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106775) f1102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2174) (RestInside.out (n := 2174) f1103 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2175) (ρ' := [(0, 2171), (1, 2174), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106777) f1103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2176) (RestInside.out (n := 2176) f1104 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2177) (ρ' := [(0, 2171), (1, 2176), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10677a) f1104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2178) (RestInside.out (n := 2178) f1105 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2179) (ρ' := [(0, 2171), (1, 2178), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10677c) f1105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2180) (RestInside.out (n := 2180) f1106 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2181) (ρ' := [(0, 2171), (1, 2180), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106782) f1106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2182) (RestInside.out (n := 2182) f1107 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2183) (ρ' := [(0, 2171), (1, 2180), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106784) f1107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2184) (RestInside.out (n := 2184) f1108 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2185) (ρ' := [(0, 2171), (1, 2184), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106787) f1108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2186) (RestInside.exec (n := 2186) (ρ' := [(0, 2171), (1, 2184), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10678c) f1109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2187) (RestInside.out (n := 2187) f1110 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2188) (ρ' := [(0, 2171), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10678e) f1110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2189) (RestInside.exec (n := 2189) (ρ' := [(0, 2171), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106793) f1111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2190) (RestInside.exec (n := 2190) (ρ' := [(0, 2171), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106798) f1112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2191) (RestInside.out (n := 2191) f1113 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2192) (ρ' := [(0, 2191), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10679f) f1113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2193) (RestInside.out (n := 2193) f1114 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2194) (ρ' := [(0, 2193), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067a1) f1114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2195) (RestInside.exec (n := 2195) (ρ' := [(0, 2193), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067a6) f1115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2196) (RestInside.out (n := 2196) f1116 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2197) (ρ' := [(0, 2196), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067ad) f1116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2198) (RestInside.out (n := 2198) f1117 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2199) (ρ' := [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067af) f1117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2200) (RestInside.exec (n := 2200) (ρ' := [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067b4) f1118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2201) (RestInside.out (n := 2201) f1119 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2202) (ρ' := [(0, 2198), (1, 2187), (2, 2182), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 2201), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1067b7) f1119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_56 code

theorem rest_l10593a_54 [Bindings] (code : CodeMap) :
    Rest (n := 2138) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 2135), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      112 0x106716 bytes_l10593a_54 b_l10593a_54 := by
  have f1080 : InstrSpec 0x106716 [0x8B, 0x84, 0x24, 0x0C, 0x01, 0x00, 0x00] (LoadPre 0x106716 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10c)) s (0x106716 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x106716 0 (.sib 4 none 0 (.d32 0x10c)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x106716 0 (.sib 4 none 0 (.d32 0x10c))).toInstrSpec (mov_r32_m32_low_effect_step 0x106716 0 (.sib 4 none 0 (.d32 0x10c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1081 : InstrSpec 0x10671d [0xF7, 0xD0] (fun s => s.RIP = 0x10671d) (notR32Effect 0x10671d 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR32Effect_footprint 0x10671d 2 0).toInstrSpec (not_r32_effect_step 0x10671d 0xd0 (by decide) (by decide)) pre_rip
  have f1082 : InstrSpec 0x10671f [0x66, 0x89, 0x44, 0x24, 0x38] (StorePre 0x10671f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10671f + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10671f 5 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10671f 5 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m16_r16_effect_step 0x10671f 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1083 : InstrSpec 0x106724 [0x8B, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00] (LoadPre 0x106724 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x106724 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x106724 0 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x106724 0 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_r32_m32_low_effect_step 0x106724 0 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1084 : InstrSpec 0x10672b [0xF7, 0xD0] (fun s => s.RIP = 0x10672b) (notR32Effect 0x10672b 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR32Effect_footprint 0x10672b 2 0).toInstrSpec (not_r32_effect_step 0x10672b 0xd0 (by decide) (by decide)) pre_rip
  have f1085 : InstrSpec 0x10672d [0x66, 0x89, 0x44, 0x24, 0x3C] (StorePre 0x10672d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x10672d + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10672d 5 0 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10672d 5 0 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_m16_r16_effect_step 0x10672d 0 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1086 : InstrSpec 0x106732 [0x66, 0xF7, 0x54, 0x24, 0x3E] (StorePre 0x106732 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x106732 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106732 5 16 (.sib 4 none 0 (.d8 0x3e)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x106732 5 (.sib 4 none 0 (.d8 0x3e))).toInstrSpec (not_m16_effect_step 0x106732 (.sib 4 none 0 (.d8 0x3e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1087 : InstrSpec 0x106737 [0x66, 0xF7, 0x54, 0x24, 0x46] (StorePre 0x106737 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x106737 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106737 5 16 (.sib 4 none 0 (.d8 0x46)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x106737 5 (.sib 4 none 0 (.d8 0x46))).toInstrSpec (not_m16_effect_step 0x106737 (.sib 4 none 0 (.d8 0x46)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1088 : InstrSpec 0x10673c [0x89, 0xCF] (fun s => s.RIP = 0x10673c) (movR32R32Effect 0x10673c 2 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x10673c 2 7 1).toInstrSpec (mov_r32_r32_effect_step 0x10673c 0xcf (by decide)) pre_rip
  have f1089 : InstrSpec 0x10673e [0xD1, 0xEF] (fun s => s.RIP = 0x10673e) (shrR32Effect 0x10673e 2 7 1)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x10673e 2 7 1).toInstrSpec (shr_r32_one_effect_step 0x10673e 0xef (by decide) (by decide)) pre_rip
  have f1090 : InstrSpec 0x106740 [0x66, 0xF7, 0x54, 0x24, 0x48] (StorePre 0x106740 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x106740 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106740 5 16 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x106740 5 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (not_m16_effect_step 0x106740 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1091 : InstrSpec 0x106745 [0x31, 0xCF] (fun s => s.RIP = 0x106745) (xorR32R32Effect 0x106745 2 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106745 2 7 1).toInstrSpec (xor_r32_r32_effect_step 0x106745 0xcf (by decide)) pre_rip
  have f1092 : InstrSpec 0x106747 [0x66, 0xF7, 0x54, 0x24, 0x4C] (StorePre 0x106747 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x106747 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106747 5 16 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x106747 5 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (not_m16_effect_step 0x106747 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1093 : InstrSpec 0x10674c [0x81, 0xE7, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x10674c) (andR32Imm32Effect 0x10674c 6 7 0x5050)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10674c 6 7 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x10674c 0xe7 0x5050 (by decide) (by decide)) pre_rip
  have f1094 : InstrSpec 0x106752 [0x66, 0xF7, 0x54, 0x24, 0x4E] (StorePre 0x106752 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4e)) s (0x106752 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106752 5 16 (.sib 4 none 0 (.d8 0x4e)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x106752 5 (.sib 4 none 0 (.d8 0x4e))).toInstrSpec (not_m16_effect_step 0x106752 (.sib 4 none 0 (.d8 0x4e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1095 : InstrSpec 0x106757 [0x31, 0xF9] (fun s => s.RIP = 0x106757) (xorR32R32Effect 0x106757 2 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106757 2 1 7).toInstrSpec (xor_r32_r32_effect_step 0x106757 0xf9 (by decide)) pre_rip
  have f1096 : InstrSpec 0x106759 [0x66, 0xF7, 0x54, 0x24, 0x56] (StorePre 0x106759 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x56)) s (0x106759 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106759 5 16 (.sib 4 none 0 (.d8 0x56)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x106759 5 (.sib 4 none 0 (.d8 0x56))).toInstrSpec (not_m16_effect_step 0x106759 (.sib 4 none 0 (.d8 0x56)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1097 : InstrSpec 0x10675e [0x01, 0xFF] (fun s => s.RIP = 0x10675e) (addR32R32Effect 0x10675e 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10675e 2 7 7).toInstrSpec (add_r32_r32_effect_step 0x10675e 0xff (by decide)) pre_rip
  have f1098 : InstrSpec 0x106760 [0x66, 0xF7, 0x54, 0x24, 0x58] (StorePre 0x106760 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x106760 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106760 5 16 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x106760 5 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (not_m16_effect_step 0x106760 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1099 : InstrSpec 0x106765 [0x31, 0xCF] (fun s => s.RIP = 0x106765) (xorR32R32Effect 0x106765 2 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106765 2 7 1).toInstrSpec (xor_r32_r32_effect_step 0x106765 0xcf (by decide)) pre_rip
  refine Rest.ofInside (n := 2138) (RestInside.out (n := 2138) f1080 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2139) (ρ' := [(0, 2138), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10671d) f1080 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2140) (RestInside.out (n := 2140) f1081 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2141) (ρ' := [(0, 2140), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10671f) f1081 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2142) (RestInside.exec (n := 2142) (ρ' := [(0, 2140), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106724) f1082 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2143) (RestInside.out (n := 2143) f1083 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2144) (ρ' := [(0, 2143), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10672b) f1083 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2145) (RestInside.out (n := 2145) f1084 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2146) (ρ' := [(0, 2145), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10672d) f1084 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2147) (RestInside.exec (n := 2147) (ρ' := [(0, 2145), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106732) f1085 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2148) (RestInside.exec (n := 2148) (ρ' := [(0, 2145), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106737) f1086 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2149) (RestInside.exec (n := 2149) (ρ' := [(0, 2145), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10673c) f1087 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2150) (RestInside.out (n := 2150) f1088 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2151) (ρ' := [(0, 2145), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2150), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10673e) f1088 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2152) (RestInside.out (n := 2152) f1089 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2153) (ρ' := [(0, 2145), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2152), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106740) f1089 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2154) (RestInside.exec (n := 2154) (ρ' := [(0, 2145), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2152), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106745) f1090 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2155) (RestInside.out (n := 2155) f1091 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2156) (ρ' := [(0, 2145), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2155), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106747) f1091 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2157) (RestInside.exec (n := 2157) (ρ' := [(0, 2145), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2155), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10674c) f1092 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2158) (RestInside.out (n := 2158) f1093 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2159) (ρ' := [(0, 2145), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2158), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106752) f1093 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2160) (RestInside.exec (n := 2160) (ρ' := [(0, 2145), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2158), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106757) f1094 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2161) (RestInside.out (n := 2161) f1095 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2162) (ρ' := [(0, 2145), (1, 2161), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2158), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106759) f1095 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2163) (RestInside.exec (n := 2163) (ρ' := [(0, 2145), (1, 2161), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2158), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10675e) f1096 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2164) (RestInside.out (n := 2164) f1097 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2165) (ρ' := [(0, 2145), (1, 2161), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2164), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106760) f1097 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2166) (RestInside.exec (n := 2166) (ρ' := [(0, 2145), (1, 2161), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2164), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106765) f1098 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2167) (RestInside.out (n := 2167) f1099 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2168) (ρ' := [(0, 2145), (1, 2161), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2167), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106767) f1099 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_55 code

theorem rest_l10593a_53 [Bindings] (code : CodeMap) :
    Rest (n := 2105) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 2103), (1, 2090), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      132 0x1066c4 bytes_l10593a_53 b_l10593a_53 := by
  have f1060 : InstrSpec 0x1066c4 [0x66, 0x89, 0x44, 0x24, 0x1C] (StorePre 0x1066c4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1066c4 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1066c4 5 0 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1066c4 5 0 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m16_r16_effect_step 0x1066c4 0 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1061 : InstrSpec 0x1066c9 [0x89, 0xF9] (fun s => s.RIP = 0x1066c9) (movR32R32Effect 0x1066c9 2 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1066c9 2 1 7).toInstrSpec (mov_r32_r32_effect_step 0x1066c9 0xf9 (by decide)) pre_rip
  have f1062 : InstrSpec 0x1066cb [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x1066cb) (shrR32Effect 0x1066cb 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1066cb 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x1066cb 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f1063 : InstrSpec 0x1066ce [0x31, 0xF9] (fun s => s.RIP = 0x1066ce) (xorR32R32Effect 0x1066ce 2 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1066ce 2 1 7).toInstrSpec (xor_r32_r32_effect_step 0x1066ce 0xf9 (by decide)) pre_rip
  have f1064 : InstrSpec 0x1066d0 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x1066d0) (andR32Imm32Effect 0x1066d0 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1066d0 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x1066d0 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f1065 : InstrSpec 0x1066d6 [0x31, 0xCF] (fun s => s.RIP = 0x1066d6) (xorR32R32Effect 0x1066d6 2 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1066d6 2 7 1).toInstrSpec (xor_r32_r32_effect_step 0x1066d6 0xcf (by decide)) pre_rip
  have f1066 : InstrSpec 0x1066d8 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x1066d8) (shlR32Effect 0x1066d8 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x1066d8 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x1066d8 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f1067 : InstrSpec 0x1066db [0x66, 0xF7, 0x54, 0x24, 0x1E] (StorePre 0x1066db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x1066db + BitVec.ofNat 64 5)) 2) (notMEffect 0x1066db 5 16 (.sib 4 none 0 (.d8 0x1e)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x1066db 5 (.sib 4 none 0 (.d8 0x1e))).toInstrSpec (not_m16_effect_step 0x1066db (.sib 4 none 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1068 : InstrSpec 0x1066e0 [0x31, 0xF9] (fun s => s.RIP = 0x1066e0) (xorR32R32Effect 0x1066e0 2 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1066e0 2 1 7).toInstrSpec (xor_r32_r32_effect_step 0x1066e0 0xf9 (by decide)) pre_rip
  have f1069 : InstrSpec 0x1066e2 [0x66, 0xF7, 0x54, 0x24, 0x26] (StorePre 0x1066e2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x1066e2 + BitVec.ofNat 64 5)) 2) (notMEffect 0x1066e2 5 16 (.sib 4 none 0 (.d8 0x26)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x1066e2 5 (.sib 4 none 0 (.d8 0x26))).toInstrSpec (not_m16_effect_step 0x1066e2 (.sib 4 none 0 (.d8 0x26)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1070 : InstrSpec 0x1066e7 [0x66, 0xF7, 0x54, 0x24, 0x28] (StorePre 0x1066e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1066e7 + BitVec.ofNat 64 5)) 2) (notMEffect 0x1066e7 5 16 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x1066e7 5 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (not_m16_effect_step 0x1066e7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1071 : InstrSpec 0x1066ec [0x8B, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00] (LoadPre 0x1066ec (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x1066ec + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1066ec 0 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1066ec 0 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_r32_m32_low_effect_step 0x1066ec 0 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1072 : InstrSpec 0x1066f3 [0xF7, 0xD0] (fun s => s.RIP = 0x1066f3) (notR32Effect 0x1066f3 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR32Effect_footprint 0x1066f3 2 0).toInstrSpec (not_r32_effect_step 0x1066f3 0xd0 (by decide) (by decide)) pre_rip
  have f1073 : InstrSpec 0x1066f5 [0x66, 0x89, 0x44, 0x24, 0x2C] (StorePre 0x1066f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x1066f5 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1066f5 5 0 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1066f5 5 0 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_m16_r16_effect_step 0x1066f5 0 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1074 : InstrSpec 0x1066fa [0x8B, 0x84, 0x24, 0x14, 0x01, 0x00, 0x00] (LoadPre 0x1066fa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x114)) s (0x1066fa + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1066fa 0 (.sib 4 none 0 (.d32 0x114)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1066fa 0 (.sib 4 none 0 (.d32 0x114))).toInstrSpec (mov_r32_m32_low_effect_step 0x1066fa 0 (.sib 4 none 0 (.d32 0x114)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1075 : InstrSpec 0x106701 [0xF7, 0xD0] (fun s => s.RIP = 0x106701) (notR32Effect 0x106701 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR32Effect_footprint 0x106701 2 0).toInstrSpec (not_r32_effect_step 0x106701 0xd0 (by decide) (by decide)) pre_rip
  have f1076 : InstrSpec 0x106703 [0x66, 0x89, 0x44, 0x24, 0x2E] (StorePre 0x106703 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2e)) s (0x106703 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106703 5 0 (.sib 4 none 0 (.d8 0x2e)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106703 5 0 (.sib 4 none 0 (.d8 0x2e))).toInstrSpec (mov_m16_r16_effect_step 0x106703 0 (.sib 4 none 0 (.d8 0x2e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1077 : InstrSpec 0x106708 [0x8B, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] (LoadPre 0x106708 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x106708 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x106708 0 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x106708 0 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_r32_m32_low_effect_step 0x106708 0 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1078 : InstrSpec 0x10670f [0xF7, 0xD0] (fun s => s.RIP = 0x10670f) (notR32Effect 0x10670f 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR32Effect_footprint 0x10670f 2 0).toInstrSpec (not_r32_effect_step 0x10670f 0xd0 (by decide) (by decide)) pre_rip
  have f1079 : InstrSpec 0x106711 [0x66, 0x89, 0x44, 0x24, 0x36] (StorePre 0x106711 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x106711 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106711 5 0 (.sib 4 none 0 (.d8 0x36)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106711 5 0 (.sib 4 none 0 (.d8 0x36))).toInstrSpec (mov_m16_r16_effect_step 0x106711 0 (.sib 4 none 0 (.d8 0x36)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 2105) (RestInside.exec (n := 2105) (ρ' := [(0, 2103), (1, 2090), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066c9) f1060 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2106) (RestInside.out (n := 2106) f1061 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2107) (ρ' := [(0, 2103), (1, 2106), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066cb) f1061 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2108) (RestInside.out (n := 2108) f1062 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2109) (ρ' := [(0, 2103), (1, 2108), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066ce) f1062 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2110) (RestInside.out (n := 2110) f1063 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2111) (ρ' := [(0, 2103), (1, 2110), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066d0) f1063 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2112) (RestInside.out (n := 2112) f1064 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2113) (ρ' := [(0, 2103), (1, 2112), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066d6) f1064 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2114) (RestInside.out (n := 2114) f1065 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2115) (ρ' := [(0, 2103), (1, 2112), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066d8) f1065 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2116) (RestInside.out (n := 2116) f1066 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2117) (ρ' := [(0, 2103), (1, 2116), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066db) f1066 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2118) (RestInside.exec (n := 2118) (ρ' := [(0, 2103), (1, 2116), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066e0) f1067 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2119) (RestInside.out (n := 2119) f1068 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2120) (ρ' := [(0, 2103), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066e2) f1068 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2121) (RestInside.exec (n := 2121) (ρ' := [(0, 2103), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066e7) f1069 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2122) (RestInside.exec (n := 2122) (ρ' := [(0, 2103), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066ec) f1070 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2123) (RestInside.out (n := 2123) f1071 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2124) (ρ' := [(0, 2123), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066f3) f1071 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2125) (RestInside.out (n := 2125) f1072 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2126) (ρ' := [(0, 2125), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066f5) f1072 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2127) (RestInside.exec (n := 2127) (ρ' := [(0, 2125), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066fa) f1073 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2128) (RestInside.out (n := 2128) f1074 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2129) (ρ' := [(0, 2128), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106701) f1074 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2130) (RestInside.out (n := 2130) f1075 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2131) (ρ' := [(0, 2130), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106703) f1075 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2132) (RestInside.exec (n := 2132) (ρ' := [(0, 2130), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106708) f1076 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2133) (RestInside.out (n := 2133) f1077 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2134) (ρ' := [(0, 2133), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10670f) f1077 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2135) (RestInside.out (n := 2135) f1078 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2136) (ρ' := [(0, 2135), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106711) f1078 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2137) (RestInside.exec (n := 2137) (ρ' := [(0, 2135), (1, 2119), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2114), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106716) f1079 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10593a_54 code

theorem rest_l10593a_52 [Bindings] (code : CodeMap) :
    Rest (n := 2066) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 2063), (1, 2059), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      152 0x106676 bytes_l10593a_52 b_l10593a_52 := by
  have f1040 : InstrSpec 0x106676 [0x0F, 0xB7, 0x84, 0x24, 0xEA, 0x00, 0x00, 0x00] (LoadPre 0x106676 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xea)) s (0x106676 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106676 8 0 (.sib 4 none 0 (.d32 0xea)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106676 8 0 (.sib 4 none 0 (.d32 0xea))).toInstrSpec (movzx_r32_m16_effect_step 0x106676 0 (.sib 4 none 0 (.d32 0xea)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1041 : InstrSpec 0x10667e [0x89, 0xC1] (fun s => s.RIP = 0x10667e) (movR32R32Effect 0x10667e 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10667e 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x10667e 0xc1 (by decide)) pre_rip
  have f1042 : InstrSpec 0x106680 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x106680) (shrR32Effect 0x106680 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x106680 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x106680 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f1043 : InstrSpec 0x106683 [0x31, 0xC1] (fun s => s.RIP = 0x106683) (xorR32R32Effect 0x106683 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106683 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106683 0xc1 (by decide)) pre_rip
  have f1044 : InstrSpec 0x106685 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x106685) (andR32Imm32Effect 0x106685 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106685 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x106685 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f1045 : InstrSpec 0x10668b [0x31, 0xC8] (fun s => s.RIP = 0x10668b) (xorR32R32Effect 0x10668b 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10668b 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10668b 0xc8 (by decide)) pre_rip
  have f1046 : InstrSpec 0x10668d [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x10668d) (shlR32Effect 0x10668d 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10668d 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x10668d 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f1047 : InstrSpec 0x106690 [0x31, 0xC1] (fun s => s.RIP = 0x106690) (xorR32R32Effect 0x106690 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106690 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106690 0xc1 (by decide)) pre_rip
  have f1048 : InstrSpec 0x106692 [0x89, 0xC8] (fun s => s.RIP = 0x106692) (movR32R32Effect 0x106692 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106692 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x106692 0xc8 (by decide)) pre_rip
  have f1049 : InstrSpec 0x106694 [0xD1, 0xE8] (fun s => s.RIP = 0x106694) (shrR32Effect 0x106694 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x106694 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x106694 0xe8 (by decide) (by decide)) pre_rip
  have f1050 : InstrSpec 0x106696 [0x31, 0xC8] (fun s => s.RIP = 0x106696) (xorR32R32Effect 0x106696 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106696 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106696 0xc8 (by decide)) pre_rip
  have f1051 : InstrSpec 0x106698 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x106698) (andEaxImm32Effect 0x106698 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106698 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x106698 0x5050) pre_rip
  have f1052 : InstrSpec 0x10669d [0x31, 0xC1] (fun s => s.RIP = 0x10669d) (xorR32R32Effect 0x10669d 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10669d 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10669d 0xc1 (by decide)) pre_rip
  have f1053 : InstrSpec 0x10669f [0x01, 0xC0] (fun s => s.RIP = 0x10669f) (addR32R32Effect 0x10669f 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10669f 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x10669f 0xc0 (by decide)) pre_rip
  have f1054 : InstrSpec 0x1066a1 [0x31, 0xC8] (fun s => s.RIP = 0x1066a1) (xorR32R32Effect 0x1066a1 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1066a1 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1066a1 0xc8 (by decide)) pre_rip
  have f1055 : InstrSpec 0x1066a3 [0x0F, 0xB7, 0x94, 0x24, 0xE6, 0x00, 0x00, 0x00] (LoadPre 0x1066a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe6)) s (0x1066a3 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1066a3 8 2 (.sib 4 none 0 (.d32 0xe6)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x1066a3 8 2 (.sib 4 none 0 (.d32 0xe6))).toInstrSpec (movzx_r32_m16_effect_step 0x1066a3 2 (.sib 4 none 0 (.d32 0xe6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1056 : InstrSpec 0x1066ab [0x0F, 0xB7, 0xB4, 0x24, 0xE8, 0x00, 0x00, 0x00] (LoadPre 0x1066ab (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1066ab + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1066ab 8 6 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M16Effect_footprint 0x1066ab 8 6 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (movzx_r32_m16_effect_step 0x1066ab 6 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1057 : InstrSpec 0x1066b3 [0x66, 0x89, 0x84, 0x24, 0xEA, 0x00, 0x00, 0x00] (StorePre 0x1066b3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xea)) s (0x1066b3 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1066b3 8 0 (.sib 4 none 0 (.d32 0xea)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1066b3 8 0 (.sib 4 none 0 (.d32 0xea))).toInstrSpec (mov_m16_r16_effect_step 0x1066b3 0 (.sib 4 none 0 (.d32 0xea)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1058 : InstrSpec 0x1066bb [0x8B, 0x84, 0x24, 0x1C, 0x01, 0x00, 0x00] (LoadPre 0x1066bb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11c)) s (0x1066bb + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1066bb 0 (.sib 4 none 0 (.d32 0x11c)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1066bb 0 (.sib 4 none 0 (.d32 0x11c))).toInstrSpec (mov_r32_m32_low_effect_step 0x1066bb 0 (.sib 4 none 0 (.d32 0x11c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1059 : InstrSpec 0x1066c2 [0xF7, 0xD0] (fun s => s.RIP = 0x1066c2) (notR32Effect 0x1066c2 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR32Effect_footprint 0x1066c2 2 0).toInstrSpec (not_r32_effect_step 0x1066c2 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 2066) (RestInside.out (n := 2066) f1040 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2067) (ρ' := [(0, 2066), (1, 2059), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10667e) f1040 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2068) (RestInside.out (n := 2068) f1041 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2069) (ρ' := [(0, 2066), (1, 2068), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106680) f1041 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2070) (RestInside.out (n := 2070) f1042 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2071) (ρ' := [(0, 2066), (1, 2070), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106683) f1042 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2072) (RestInside.out (n := 2072) f1043 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2073) (ρ' := [(0, 2066), (1, 2072), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106685) f1043 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2074) (RestInside.out (n := 2074) f1044 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2075) (ρ' := [(0, 2066), (1, 2074), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10668b) f1044 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2076) (RestInside.out (n := 2076) f1045 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2077) (ρ' := [(0, 2076), (1, 2074), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10668d) f1045 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2078) (RestInside.out (n := 2078) f1046 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2079) (ρ' := [(0, 2076), (1, 2078), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106690) f1046 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2080) (RestInside.out (n := 2080) f1047 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2081) (ρ' := [(0, 2076), (1, 2080), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106692) f1047 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2082) (RestInside.out (n := 2082) f1048 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2083) (ρ' := [(0, 2082), (1, 2080), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106694) f1048 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2084) (RestInside.out (n := 2084) f1049 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2085) (ρ' := [(0, 2084), (1, 2080), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106696) f1049 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2086) (RestInside.out (n := 2086) f1050 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2087) (ρ' := [(0, 2086), (1, 2080), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106698) f1050 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2088) (RestInside.out (n := 2088) f1051 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2089) (ρ' := [(0, 2088), (1, 2080), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10669d) f1051 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2090) (RestInside.out (n := 2090) f1052 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2091) (ρ' := [(0, 2088), (1, 2090), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10669f) f1052 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2092) (RestInside.out (n := 2092) f1053 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2093) (ρ' := [(0, 2092), (1, 2090), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066a1) f1053 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2094) (RestInside.out (n := 2094) f1054 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2095) (ρ' := [(0, 2094), (1, 2090), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066a3) f1054 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2096) (RestInside.out (n := 2096) f1055 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2097) (ρ' := [(0, 2094), (1, 2090), (2, 2096), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066ab) f1055 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2098) (RestInside.out (n := 2098) f1056 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2099) (ρ' := [(0, 2094), (1, 2090), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066b3) f1056 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2100) (RestInside.exec (n := 2100) (ρ' := [(0, 2094), (1, 2090), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066bb) f1057 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2101) (RestInside.out (n := 2101) f1058 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2102) (ρ' := [(0, 2101), (1, 2090), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066c2) f1058 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2103) (RestInside.out (n := 2103) f1059 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2104) (ρ' := [(0, 2103), (1, 2090), (2, 2096), (3, 1659), (4, 4), (5, 1592), (6, 2098), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1066c4) f1059 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_53 code

theorem rest_l10593a_51 [Bindings] (code : CodeMap) :
    Rest (n := 2028) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 2026), (1, 2018), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      172 0x106633 bytes_l10593a_51 b_l10593a_51 := by
  have f1020 : InstrSpec 0x106633 [0x31, 0xC1] (fun s => s.RIP = 0x106633) (xorR32R32Effect 0x106633 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106633 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106633 0xc1 (by decide)) pre_rip
  have f1021 : InstrSpec 0x106635 [0x01, 0xC0] (fun s => s.RIP = 0x106635) (addR32R32Effect 0x106635 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x106635 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x106635 0xc0 (by decide)) pre_rip
  have f1022 : InstrSpec 0x106637 [0x31, 0xC8] (fun s => s.RIP = 0x106637) (xorR32R32Effect 0x106637 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106637 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106637 0xc8 (by decide)) pre_rip
  have f1023 : InstrSpec 0x106639 [0x66, 0x89, 0x84, 0x24, 0xE2, 0x00, 0x00, 0x00] (StorePre 0x106639 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe2)) s (0x106639 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106639 8 0 (.sib 4 none 0 (.d32 0xe2)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106639 8 0 (.sib 4 none 0 (.d32 0xe2))).toInstrSpec (mov_m16_r16_effect_step 0x106639 0 (.sib 4 none 0 (.d32 0xe2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1024 : InstrSpec 0x106641 [0x0F, 0xB7, 0x84, 0x24, 0xE4, 0x00, 0x00, 0x00] (LoadPre 0x106641 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe4)) s (0x106641 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106641 8 0 (.sib 4 none 0 (.d32 0xe4)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106641 8 0 (.sib 4 none 0 (.d32 0xe4))).toInstrSpec (movzx_r32_m16_effect_step 0x106641 0 (.sib 4 none 0 (.d32 0xe4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1025 : InstrSpec 0x106649 [0x89, 0xC1] (fun s => s.RIP = 0x106649) (movR32R32Effect 0x106649 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106649 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x106649 0xc1 (by decide)) pre_rip
  have f1026 : InstrSpec 0x10664b [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x10664b) (shrR32Effect 0x10664b 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10664b 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x10664b 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f1027 : InstrSpec 0x10664e [0x31, 0xC1] (fun s => s.RIP = 0x10664e) (xorR32R32Effect 0x10664e 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10664e 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10664e 0xc1 (by decide)) pre_rip
  have f1028 : InstrSpec 0x106650 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x106650) (andR32Imm32Effect 0x106650 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106650 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x106650 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f1029 : InstrSpec 0x106656 [0x31, 0xC8] (fun s => s.RIP = 0x106656) (xorR32R32Effect 0x106656 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106656 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106656 0xc8 (by decide)) pre_rip
  have f1030 : InstrSpec 0x106658 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x106658) (shlR32Effect 0x106658 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x106658 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x106658 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f1031 : InstrSpec 0x10665b [0x31, 0xC1] (fun s => s.RIP = 0x10665b) (xorR32R32Effect 0x10665b 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10665b 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10665b 0xc1 (by decide)) pre_rip
  have f1032 : InstrSpec 0x10665d [0x89, 0xC8] (fun s => s.RIP = 0x10665d) (movR32R32Effect 0x10665d 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x10665d 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x10665d 0xc8 (by decide)) pre_rip
  have f1033 : InstrSpec 0x10665f [0xD1, 0xE8] (fun s => s.RIP = 0x10665f) (shrR32Effect 0x10665f 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x10665f 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x10665f 0xe8 (by decide) (by decide)) pre_rip
  have f1034 : InstrSpec 0x106661 [0x31, 0xC8] (fun s => s.RIP = 0x106661) (xorR32R32Effect 0x106661 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106661 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106661 0xc8 (by decide)) pre_rip
  have f1035 : InstrSpec 0x106663 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x106663) (andEaxImm32Effect 0x106663 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106663 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x106663 0x5050) pre_rip
  have f1036 : InstrSpec 0x106668 [0x31, 0xC1] (fun s => s.RIP = 0x106668) (xorR32R32Effect 0x106668 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106668 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106668 0xc1 (by decide)) pre_rip
  have f1037 : InstrSpec 0x10666a [0x01, 0xC0] (fun s => s.RIP = 0x10666a) (addR32R32Effect 0x10666a 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10666a 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x10666a 0xc0 (by decide)) pre_rip
  have f1038 : InstrSpec 0x10666c [0x31, 0xC8] (fun s => s.RIP = 0x10666c) (xorR32R32Effect 0x10666c 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10666c 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10666c 0xc8 (by decide)) pre_rip
  have f1039 : InstrSpec 0x10666e [0x66, 0x89, 0x84, 0x24, 0xE4, 0x00, 0x00, 0x00] (StorePre 0x10666e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe4)) s (0x10666e + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x10666e 8 0 (.sib 4 none 0 (.d32 0xe4)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10666e 8 0 (.sib 4 none 0 (.d32 0xe4))).toInstrSpec (mov_m16_r16_effect_step 0x10666e 0 (.sib 4 none 0 (.d32 0xe4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 2028) (RestInside.out (n := 2028) f1020 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2029) (ρ' := [(0, 2026), (1, 2028), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106635) f1020 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2030) (RestInside.out (n := 2030) f1021 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2031) (ρ' := [(0, 2030), (1, 2028), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106637) f1021 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2032) (RestInside.out (n := 2032) f1022 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2033) (ρ' := [(0, 2032), (1, 2028), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106639) f1022 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2034) (RestInside.exec (n := 2034) (ρ' := [(0, 2032), (1, 2028), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106641) f1023 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2035) (RestInside.out (n := 2035) f1024 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2036) (ρ' := [(0, 2035), (1, 2028), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106649) f1024 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2037) (RestInside.out (n := 2037) f1025 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2038) (ρ' := [(0, 2035), (1, 2037), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10664b) f1025 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2039) (RestInside.out (n := 2039) f1026 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2040) (ρ' := [(0, 2035), (1, 2039), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10664e) f1026 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2041) (RestInside.out (n := 2041) f1027 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2042) (ρ' := [(0, 2035), (1, 2041), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106650) f1027 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2043) (RestInside.out (n := 2043) f1028 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2044) (ρ' := [(0, 2035), (1, 2043), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106656) f1028 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2045) (RestInside.out (n := 2045) f1029 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2046) (ρ' := [(0, 2045), (1, 2043), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106658) f1029 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2047) (RestInside.out (n := 2047) f1030 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2048) (ρ' := [(0, 2045), (1, 2047), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10665b) f1030 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2049) (RestInside.out (n := 2049) f1031 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2050) (ρ' := [(0, 2045), (1, 2049), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10665d) f1031 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2051) (RestInside.out (n := 2051) f1032 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2052) (ρ' := [(0, 2051), (1, 2049), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10665f) f1032 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2053) (RestInside.out (n := 2053) f1033 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2054) (ρ' := [(0, 2053), (1, 2049), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106661) f1033 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2055) (RestInside.out (n := 2055) f1034 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2056) (ρ' := [(0, 2055), (1, 2049), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106663) f1034 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2057) (RestInside.out (n := 2057) f1035 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2058) (ρ' := [(0, 2057), (1, 2049), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106668) f1035 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2059) (RestInside.out (n := 2059) f1036 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2060) (ρ' := [(0, 2057), (1, 2059), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10666a) f1036 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2061) (RestInside.out (n := 2061) f1037 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2062) (ρ' := [(0, 2061), (1, 2059), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10666c) f1037 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2063) (RestInside.out (n := 2063) f1038 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2064) (ρ' := [(0, 2063), (1, 2059), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10666e) f1038 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2065) (RestInside.exec (n := 2065) (ρ' := [(0, 2063), (1, 2059), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106676) f1039 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10593a_52 code

theorem rest_l10593a_50 [Bindings] (code : CodeMap) :
    Rest (n := 1989) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1987), (1, 1985), (3, 1659), (4, 4), (5, 1592), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      192 0x1065ed bytes_l10593a_50 b_l10593a_50 := by
  have f1000 : InstrSpec 0x1065ed [0xD1, 0xE8] (fun s => s.RIP = 0x1065ed) (shrR32Effect 0x1065ed 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x1065ed 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x1065ed 0xe8 (by decide) (by decide)) pre_rip
  have f1001 : InstrSpec 0x1065ef [0x31, 0xC8] (fun s => s.RIP = 0x1065ef) (xorR32R32Effect 0x1065ef 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1065ef 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1065ef 0xc8 (by decide)) pre_rip
  have f1002 : InstrSpec 0x1065f1 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1065f1) (andEaxImm32Effect 0x1065f1 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x1065f1 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x1065f1 0x5050) pre_rip
  have f1003 : InstrSpec 0x1065f6 [0x31, 0xC1] (fun s => s.RIP = 0x1065f6) (xorR32R32Effect 0x1065f6 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1065f6 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1065f6 0xc1 (by decide)) pre_rip
  have f1004 : InstrSpec 0x1065f8 [0x01, 0xC0] (fun s => s.RIP = 0x1065f8) (addR32R32Effect 0x1065f8 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1065f8 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x1065f8 0xc0 (by decide)) pre_rip
  have f1005 : InstrSpec 0x1065fa [0x31, 0xC8] (fun s => s.RIP = 0x1065fa) (xorR32R32Effect 0x1065fa 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1065fa 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1065fa 0xc8 (by decide)) pre_rip
  have f1006 : InstrSpec 0x1065fc [0x0F, 0xB7, 0xBC, 0x24, 0xDE, 0x00, 0x00, 0x00] (LoadPre 0x1065fc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xde)) s (0x1065fc + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1065fc 8 7 (.sib 4 none 0 (.d32 0xde)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M16Effect_footprint 0x1065fc 8 7 (.sib 4 none 0 (.d32 0xde))).toInstrSpec (movzx_r32_m16_effect_step 0x1065fc 7 (.sib 4 none 0 (.d32 0xde)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1007 : InstrSpec 0x106604 [0x66, 0x89, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x106604 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x106604 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106604 8 0 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106604 8 0 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_m16_r16_effect_step 0x106604 0 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1008 : InstrSpec 0x10660c [0x0F, 0xB7, 0x84, 0x24, 0xE2, 0x00, 0x00, 0x00] (LoadPre 0x10660c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe2)) s (0x10660c + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x10660c 8 0 (.sib 4 none 0 (.d32 0xe2)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10660c 8 0 (.sib 4 none 0 (.d32 0xe2))).toInstrSpec (movzx_r32_m16_effect_step 0x10660c 0 (.sib 4 none 0 (.d32 0xe2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1009 : InstrSpec 0x106614 [0x89, 0xC1] (fun s => s.RIP = 0x106614) (movR32R32Effect 0x106614 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106614 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x106614 0xc1 (by decide)) pre_rip
  have f1010 : InstrSpec 0x106616 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x106616) (shrR32Effect 0x106616 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x106616 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x106616 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f1011 : InstrSpec 0x106619 [0x31, 0xC1] (fun s => s.RIP = 0x106619) (xorR32R32Effect 0x106619 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106619 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106619 0xc1 (by decide)) pre_rip
  have f1012 : InstrSpec 0x10661b [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x10661b) (andR32Imm32Effect 0x10661b 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10661b 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x10661b 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f1013 : InstrSpec 0x106621 [0x31, 0xC8] (fun s => s.RIP = 0x106621) (xorR32R32Effect 0x106621 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106621 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106621 0xc8 (by decide)) pre_rip
  have f1014 : InstrSpec 0x106623 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x106623) (shlR32Effect 0x106623 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x106623 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x106623 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f1015 : InstrSpec 0x106626 [0x31, 0xC1] (fun s => s.RIP = 0x106626) (xorR32R32Effect 0x106626 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106626 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106626 0xc1 (by decide)) pre_rip
  have f1016 : InstrSpec 0x106628 [0x89, 0xC8] (fun s => s.RIP = 0x106628) (movR32R32Effect 0x106628 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106628 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x106628 0xc8 (by decide)) pre_rip
  have f1017 : InstrSpec 0x10662a [0xD1, 0xE8] (fun s => s.RIP = 0x10662a) (shrR32Effect 0x10662a 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x10662a 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x10662a 0xe8 (by decide) (by decide)) pre_rip
  have f1018 : InstrSpec 0x10662c [0x31, 0xC8] (fun s => s.RIP = 0x10662c) (xorR32R32Effect 0x10662c 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10662c 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10662c 0xc8 (by decide)) pre_rip
  have f1019 : InstrSpec 0x10662e [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x10662e) (andEaxImm32Effect 0x10662e 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x10662e 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x10662e 0x5050) pre_rip
  refine Rest.ofInside (n := 1989) (RestInside.out (n := 1989) f1000 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1990) (ρ' := [(0, 1989), (1, 1985), (3, 1659), (4, 4), (5, 1592), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065ef) f1000 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1991) (RestInside.out (n := 1991) f1001 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1992) (ρ' := [(0, 1991), (1, 1985), (3, 1659), (4, 4), (5, 1592), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065f1) f1001 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1993) (RestInside.out (n := 1993) f1002 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1994) (ρ' := [(0, 1993), (1, 1985), (3, 1659), (4, 4), (5, 1592), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065f6) f1002 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1995) (RestInside.out (n := 1995) f1003 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1996) (ρ' := [(0, 1993), (1, 1995), (3, 1659), (4, 4), (5, 1592), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065f8) f1003 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1997) (RestInside.out (n := 1997) f1004 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1998) (ρ' := [(0, 1997), (1, 1995), (3, 1659), (4, 4), (5, 1592), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065fa) f1004 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1999) (RestInside.out (n := 1999) f1005 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2000) (ρ' := [(0, 1999), (1, 1995), (3, 1659), (4, 4), (5, 1592), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065fc) f1005 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2001) (RestInside.out (n := 2001) f1006 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2002) (ρ' := [(0, 1999), (1, 1995), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106604) f1006 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2003) (RestInside.exec (n := 2003) (ρ' := [(0, 1999), (1, 1995), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10660c) f1007 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 2004) (RestInside.out (n := 2004) f1008 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2005) (ρ' := [(0, 2004), (1, 1995), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106614) f1008 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2006) (RestInside.out (n := 2006) f1009 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2007) (ρ' := [(0, 2004), (1, 2006), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106616) f1009 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2008) (RestInside.out (n := 2008) f1010 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2009) (ρ' := [(0, 2004), (1, 2008), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106619) f1010 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2010) (RestInside.out (n := 2010) f1011 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2011) (ρ' := [(0, 2004), (1, 2010), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10661b) f1011 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2012) (RestInside.out (n := 2012) f1012 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2013) (ρ' := [(0, 2004), (1, 2012), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106621) f1012 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2014) (RestInside.out (n := 2014) f1013 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2015) (ρ' := [(0, 2014), (1, 2012), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106623) f1013 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2016) (RestInside.out (n := 2016) f1014 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2017) (ρ' := [(0, 2014), (1, 2016), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106626) f1014 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2018) (RestInside.out (n := 2018) f1015 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2019) (ρ' := [(0, 2014), (1, 2018), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106628) f1015 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2020) (RestInside.out (n := 2020) f1016 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2021) (ρ' := [(0, 2020), (1, 2018), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10662a) f1016 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2022) (RestInside.out (n := 2022) f1017 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2023) (ρ' := [(0, 2022), (1, 2018), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10662c) f1017 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2024) (RestInside.out (n := 2024) f1018 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2025) (ρ' := [(0, 2024), (1, 2018), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10662e) f1018 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 2026) (RestInside.out (n := 2026) f1019 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 2027) (ρ' := [(0, 2026), (1, 2018), (3, 1659), (4, 4), (5, 1592), (7, 2001), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106633) f1019 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_51 code

theorem rest_l10593a_49 [Bindings] (code : CodeMap) :
    Rest (n := 1949) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1941), (1, 1947), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      212 0x1065a9 bytes_l10593a_49 b_l10593a_49 := by
  have f980 : InstrSpec 0x1065a9 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x1065a9) (andR32Imm32Effect 0x1065a9 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1065a9 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x1065a9 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f981 : InstrSpec 0x1065af [0x31, 0xC8] (fun s => s.RIP = 0x1065af) (xorR32R32Effect 0x1065af 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1065af 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1065af 0xc8 (by decide)) pre_rip
  have f982 : InstrSpec 0x1065b1 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x1065b1) (shlR32Effect 0x1065b1 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x1065b1 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x1065b1 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f983 : InstrSpec 0x1065b4 [0x31, 0xC1] (fun s => s.RIP = 0x1065b4) (xorR32R32Effect 0x1065b4 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1065b4 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1065b4 0xc1 (by decide)) pre_rip
  have f984 : InstrSpec 0x1065b6 [0x41, 0x89, 0xC8] (fun s => s.RIP = 0x1065b6) (movR32R32Effect 0x1065b6 3 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x1065b6 3 8 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x1065b6 0x41 0xc8 (by decide) (by decide)) pre_rip
  have f985 : InstrSpec 0x1065b9 [0x41, 0xD1, 0xE8] (fun s => s.RIP = 0x1065b9) (shrR32Effect 0x1065b9 3 8 1)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR32Effect_footprint 0x1065b9 3 8 1).toInstrSpec (shr_r32_one_rex_effect_step 0x1065b9 0x41 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f986 : InstrSpec 0x1065bc [0x41, 0x31, 0xC8] (fun s => s.RIP = 0x1065bc) (xorR32R32Effect 0x1065bc 3 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1065bc 3 8 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x1065bc 0x41 0xc8 (by decide) (by decide)) pre_rip
  have f987 : InstrSpec 0x1065bf [0x41, 0x81, 0xE0, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1065bf) (andR32Imm32Effect 0x1065bf 7 8 0x5050)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1065bf 7 8 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x1065bf 0x41 0xe0 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f988 : InstrSpec 0x1065c6 [0x44, 0x31, 0xC1] (fun s => s.RIP = 0x1065c6) (xorR32R32Effect 0x1065c6 3 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1065c6 3 1 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1065c6 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f989 : InstrSpec 0x1065c9 [0x45, 0x01, 0xC0] (fun s => s.RIP = 0x1065c9) (addR32R32Effect 0x1065c9 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1065c9 3 8 8).toInstrSpec (add_r32_r32_rex_effect_step 0x1065c9 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f990 : InstrSpec 0x1065cc [0x41, 0x31, 0xC8] (fun s => s.RIP = 0x1065cc) (xorR32R32Effect 0x1065cc 3 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1065cc 3 8 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x1065cc 0x41 0xc8 (by decide) (by decide)) pre_rip
  have f991 : InstrSpec 0x1065cf [0x0F, 0xB7, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00] (LoadPre 0x1065cf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1065cf + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1065cf 8 0 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1065cf 8 0 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (movzx_r32_m16_effect_step 0x1065cf 0 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f992 : InstrSpec 0x1065d7 [0x89, 0xC1] (fun s => s.RIP = 0x1065d7) (movR32R32Effect 0x1065d7 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1065d7 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1065d7 0xc1 (by decide)) pre_rip
  have f993 : InstrSpec 0x1065d9 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x1065d9) (shrR32Effect 0x1065d9 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1065d9 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x1065d9 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f994 : InstrSpec 0x1065dc [0x31, 0xC1] (fun s => s.RIP = 0x1065dc) (xorR32R32Effect 0x1065dc 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1065dc 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1065dc 0xc1 (by decide)) pre_rip
  have f995 : InstrSpec 0x1065de [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x1065de) (andR32Imm32Effect 0x1065de 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1065de 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x1065de 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f996 : InstrSpec 0x1065e4 [0x31, 0xC8] (fun s => s.RIP = 0x1065e4) (xorR32R32Effect 0x1065e4 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1065e4 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1065e4 0xc8 (by decide)) pre_rip
  have f997 : InstrSpec 0x1065e6 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x1065e6) (shlR32Effect 0x1065e6 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x1065e6 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x1065e6 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f998 : InstrSpec 0x1065e9 [0x31, 0xC1] (fun s => s.RIP = 0x1065e9) (xorR32R32Effect 0x1065e9 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1065e9 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1065e9 0xc1 (by decide)) pre_rip
  have f999 : InstrSpec 0x1065eb [0x89, 0xC8] (fun s => s.RIP = 0x1065eb) (movR32R32Effect 0x1065eb 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1065eb 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x1065eb 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 1949) (RestInside.out (n := 1949) f980 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1950) (ρ' := [(0, 1941), (1, 1949), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065af) f980 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1951) (RestInside.out (n := 1951) f981 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1952) (ρ' := [(0, 1951), (1, 1949), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065b1) f981 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1953) (RestInside.out (n := 1953) f982 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1954) (ρ' := [(0, 1951), (1, 1953), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065b4) f982 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1955) (RestInside.out (n := 1955) f983 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1956) (ρ' := [(0, 1951), (1, 1955), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065b6) f983 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1957) (RestInside.out (n := 1957) f984 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1958) (ρ' := [(0, 1951), (1, 1955), (3, 1659), (4, 4), (5, 1592), (8, 1957), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065b9) f984 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1959) (RestInside.out (n := 1959) f985 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1960) (ρ' := [(0, 1951), (1, 1955), (3, 1659), (4, 4), (5, 1592), (8, 1959), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065bc) f985 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1961) (RestInside.out (n := 1961) f986 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1962) (ρ' := [(0, 1951), (1, 1955), (3, 1659), (4, 4), (5, 1592), (8, 1961), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065bf) f986 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1963) (RestInside.out (n := 1963) f987 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1964) (ρ' := [(0, 1951), (1, 1955), (3, 1659), (4, 4), (5, 1592), (8, 1963), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065c6) f987 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1965) (RestInside.out (n := 1965) f988 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1966) (ρ' := [(0, 1951), (1, 1965), (3, 1659), (4, 4), (5, 1592), (8, 1963), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065c9) f988 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1967) (RestInside.out (n := 1967) f989 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1968) (ρ' := [(0, 1951), (1, 1965), (3, 1659), (4, 4), (5, 1592), (8, 1967), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065cc) f989 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1969) (RestInside.out (n := 1969) f990 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1970) (ρ' := [(0, 1951), (1, 1965), (3, 1659), (4, 4), (5, 1592), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065cf) f990 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1971) (RestInside.out (n := 1971) f991 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1972) (ρ' := [(0, 1971), (1, 1965), (3, 1659), (4, 4), (5, 1592), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065d7) f991 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1973) (RestInside.out (n := 1973) f992 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1974) (ρ' := [(0, 1971), (1, 1973), (3, 1659), (4, 4), (5, 1592), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065d9) f992 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1975) (RestInside.out (n := 1975) f993 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1976) (ρ' := [(0, 1971), (1, 1975), (3, 1659), (4, 4), (5, 1592), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065dc) f993 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1977) (RestInside.out (n := 1977) f994 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1978) (ρ' := [(0, 1971), (1, 1977), (3, 1659), (4, 4), (5, 1592), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065de) f994 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1979) (RestInside.out (n := 1979) f995 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1980) (ρ' := [(0, 1971), (1, 1979), (3, 1659), (4, 4), (5, 1592), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065e4) f995 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1981) (RestInside.out (n := 1981) f996 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1982) (ρ' := [(0, 1981), (1, 1979), (3, 1659), (4, 4), (5, 1592), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065e6) f996 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1983) (RestInside.out (n := 1983) f997 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1984) (ρ' := [(0, 1981), (1, 1983), (3, 1659), (4, 4), (5, 1592), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065e9) f997 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1985) (RestInside.out (n := 1985) f998 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1986) (ρ' := [(0, 1981), (1, 1985), (3, 1659), (4, 4), (5, 1592), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065eb) f998 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1987) (RestInside.out (n := 1987) f999 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1988) (ρ' := [(0, 1987), (1, 1985), (3, 1659), (4, 4), (5, 1592), (8, 1969), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065ed) f999 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_50 code

theorem rest_l10593a_48 [Bindings] (code : CodeMap) :
    Rest (n := 1910) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1907), (1, 1903), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      232 0x106565 bytes_l10593a_48 b_l10593a_48 := by
  have f960 : InstrSpec 0x106565 [0x0F, 0xB7, 0x84, 0x24, 0xCA, 0x00, 0x00, 0x00] (LoadPre 0x106565 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xca)) s (0x106565 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106565 8 0 (.sib 4 none 0 (.d32 0xca)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106565 8 0 (.sib 4 none 0 (.d32 0xca))).toInstrSpec (movzx_r32_m16_effect_step 0x106565 0 (.sib 4 none 0 (.d32 0xca)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f961 : InstrSpec 0x10656d [0x89, 0xC1] (fun s => s.RIP = 0x10656d) (movR32R32Effect 0x10656d 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10656d 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x10656d 0xc1 (by decide)) pre_rip
  have f962 : InstrSpec 0x10656f [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x10656f) (shrR32Effect 0x10656f 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10656f 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x10656f 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f963 : InstrSpec 0x106572 [0x31, 0xC1] (fun s => s.RIP = 0x106572) (xorR32R32Effect 0x106572 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106572 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106572 0xc1 (by decide)) pre_rip
  have f964 : InstrSpec 0x106574 [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x106574) (andR32Imm32Effect 0x106574 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106574 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x106574 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f965 : InstrSpec 0x10657a [0x31, 0xC8] (fun s => s.RIP = 0x10657a) (xorR32R32Effect 0x10657a 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10657a 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10657a 0xc8 (by decide)) pre_rip
  have f966 : InstrSpec 0x10657c [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x10657c) (shlR32Effect 0x10657c 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10657c 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x10657c 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f967 : InstrSpec 0x10657f [0x31, 0xC1] (fun s => s.RIP = 0x10657f) (xorR32R32Effect 0x10657f 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10657f 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10657f 0xc1 (by decide)) pre_rip
  have f968 : InstrSpec 0x106581 [0x89, 0xC8] (fun s => s.RIP = 0x106581) (movR32R32Effect 0x106581 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106581 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x106581 0xc8 (by decide)) pre_rip
  have f969 : InstrSpec 0x106583 [0xD1, 0xE8] (fun s => s.RIP = 0x106583) (shrR32Effect 0x106583 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x106583 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x106583 0xe8 (by decide) (by decide)) pre_rip
  have f970 : InstrSpec 0x106585 [0x31, 0xC8] (fun s => s.RIP = 0x106585) (xorR32R32Effect 0x106585 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106585 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106585 0xc8 (by decide)) pre_rip
  have f971 : InstrSpec 0x106587 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x106587) (andEaxImm32Effect 0x106587 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106587 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x106587 0x5050) pre_rip
  have f972 : InstrSpec 0x10658c [0x31, 0xC1] (fun s => s.RIP = 0x10658c) (xorR32R32Effect 0x10658c 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10658c 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10658c 0xc1 (by decide)) pre_rip
  have f973 : InstrSpec 0x10658e [0x01, 0xC0] (fun s => s.RIP = 0x10658e) (addR32R32Effect 0x10658e 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10658e 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x10658e 0xc0 (by decide)) pre_rip
  have f974 : InstrSpec 0x106590 [0x31, 0xC8] (fun s => s.RIP = 0x106590) (xorR32R32Effect 0x106590 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106590 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106590 0xc8 (by decide)) pre_rip
  have f975 : InstrSpec 0x106592 [0x66, 0x89, 0x84, 0x24, 0xCA, 0x00, 0x00, 0x00] (StorePre 0x106592 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xca)) s (0x106592 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106592 8 0 (.sib 4 none 0 (.d32 0xca)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106592 8 0 (.sib 4 none 0 (.d32 0xca))).toInstrSpec (mov_m16_r16_effect_step 0x106592 0 (.sib 4 none 0 (.d32 0xca)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f976 : InstrSpec 0x10659a [0x0F, 0xB7, 0x84, 0x24, 0xDC, 0x00, 0x00, 0x00] (LoadPre 0x10659a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xdc)) s (0x10659a + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x10659a 8 0 (.sib 4 none 0 (.d32 0xdc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10659a 8 0 (.sib 4 none 0 (.d32 0xdc))).toInstrSpec (movzx_r32_m16_effect_step 0x10659a 0 (.sib 4 none 0 (.d32 0xdc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f977 : InstrSpec 0x1065a2 [0x89, 0xC1] (fun s => s.RIP = 0x1065a2) (movR32R32Effect 0x1065a2 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1065a2 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1065a2 0xc1 (by decide)) pre_rip
  have f978 : InstrSpec 0x1065a4 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x1065a4) (shrR32Effect 0x1065a4 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1065a4 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x1065a4 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f979 : InstrSpec 0x1065a7 [0x31, 0xC1] (fun s => s.RIP = 0x1065a7) (xorR32R32Effect 0x1065a7 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1065a7 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1065a7 0xc1 (by decide)) pre_rip
  refine Rest.ofInside (n := 1910) (RestInside.out (n := 1910) f960 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1911) (ρ' := [(0, 1910), (1, 1903), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10656d) f960 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1912) (RestInside.out (n := 1912) f961 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1913) (ρ' := [(0, 1910), (1, 1912), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10656f) f961 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1914) (RestInside.out (n := 1914) f962 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1915) (ρ' := [(0, 1910), (1, 1914), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106572) f962 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1916) (RestInside.out (n := 1916) f963 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1917) (ρ' := [(0, 1910), (1, 1916), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106574) f963 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1918) (RestInside.out (n := 1918) f964 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1919) (ρ' := [(0, 1910), (1, 1918), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10657a) f964 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1920) (RestInside.out (n := 1920) f965 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1921) (ρ' := [(0, 1920), (1, 1918), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10657c) f965 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1922) (RestInside.out (n := 1922) f966 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1923) (ρ' := [(0, 1920), (1, 1922), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10657f) f966 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1924) (RestInside.out (n := 1924) f967 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1925) (ρ' := [(0, 1920), (1, 1924), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106581) f967 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1926) (RestInside.out (n := 1926) f968 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1927) (ρ' := [(0, 1926), (1, 1924), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106583) f968 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1928) (RestInside.out (n := 1928) f969 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1929) (ρ' := [(0, 1928), (1, 1924), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106585) f969 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1930) (RestInside.out (n := 1930) f970 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1931) (ρ' := [(0, 1930), (1, 1924), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106587) f970 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1932) (RestInside.out (n := 1932) f971 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1933) (ρ' := [(0, 1932), (1, 1924), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10658c) f971 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1934) (RestInside.out (n := 1934) f972 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1935) (ρ' := [(0, 1932), (1, 1934), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10658e) f972 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1936) (RestInside.out (n := 1936) f973 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1937) (ρ' := [(0, 1936), (1, 1934), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106590) f973 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1938) (RestInside.out (n := 1938) f974 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1939) (ρ' := [(0, 1938), (1, 1934), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106592) f974 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1940) (RestInside.exec (n := 1940) (ρ' := [(0, 1938), (1, 1934), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10659a) f975 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1941) (RestInside.out (n := 1941) f976 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1942) (ρ' := [(0, 1941), (1, 1934), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065a2) f976 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1943) (RestInside.out (n := 1943) f977 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1944) (ρ' := [(0, 1941), (1, 1943), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065a4) f977 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1945) (RestInside.out (n := 1945) f978 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1946) (ρ' := [(0, 1941), (1, 1945), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065a7) f978 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1947) (RestInside.out (n := 1947) f979 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1948) (ρ' := [(0, 1941), (1, 1947), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065a9) f979 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_49 code

theorem rest_l10593a_47 [Bindings] (code : CodeMap) :
    Rest (n := 1872) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1870), (1, 1862), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      252 0x106522 bytes_l10593a_47 b_l10593a_47 := by
  have f940 : InstrSpec 0x106522 [0x31, 0xC1] (fun s => s.RIP = 0x106522) (xorR32R32Effect 0x106522 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106522 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106522 0xc1 (by decide)) pre_rip
  have f941 : InstrSpec 0x106524 [0x01, 0xC0] (fun s => s.RIP = 0x106524) (addR32R32Effect 0x106524 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x106524 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x106524 0xc0 (by decide)) pre_rip
  have f942 : InstrSpec 0x106526 [0x31, 0xC8] (fun s => s.RIP = 0x106526) (xorR32R32Effect 0x106526 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106526 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106526 0xc8 (by decide)) pre_rip
  have f943 : InstrSpec 0x106528 [0x66, 0x89, 0x84, 0x24, 0xC6, 0x00, 0x00, 0x00] (StorePre 0x106528 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc6)) s (0x106528 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106528 8 0 (.sib 4 none 0 (.d32 0xc6)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106528 8 0 (.sib 4 none 0 (.d32 0xc6))).toInstrSpec (mov_m16_r16_effect_step 0x106528 0 (.sib 4 none 0 (.d32 0xc6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f944 : InstrSpec 0x106530 [0x0F, 0xB7, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x106530 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x106530 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106530 8 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106530 8 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (movzx_r32_m16_effect_step 0x106530 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f945 : InstrSpec 0x106538 [0x89, 0xC1] (fun s => s.RIP = 0x106538) (movR32R32Effect 0x106538 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106538 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x106538 0xc1 (by decide)) pre_rip
  have f946 : InstrSpec 0x10653a [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x10653a) (shrR32Effect 0x10653a 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10653a 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x10653a 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f947 : InstrSpec 0x10653d [0x31, 0xC1] (fun s => s.RIP = 0x10653d) (xorR32R32Effect 0x10653d 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10653d 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10653d 0xc1 (by decide)) pre_rip
  have f948 : InstrSpec 0x10653f [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x10653f) (andR32Imm32Effect 0x10653f 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10653f 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x10653f 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f949 : InstrSpec 0x106545 [0x31, 0xC8] (fun s => s.RIP = 0x106545) (xorR32R32Effect 0x106545 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106545 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106545 0xc8 (by decide)) pre_rip
  have f950 : InstrSpec 0x106547 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x106547) (shlR32Effect 0x106547 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x106547 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x106547 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f951 : InstrSpec 0x10654a [0x31, 0xC1] (fun s => s.RIP = 0x10654a) (xorR32R32Effect 0x10654a 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10654a 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10654a 0xc1 (by decide)) pre_rip
  have f952 : InstrSpec 0x10654c [0x89, 0xC8] (fun s => s.RIP = 0x10654c) (movR32R32Effect 0x10654c 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x10654c 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x10654c 0xc8 (by decide)) pre_rip
  have f953 : InstrSpec 0x10654e [0xD1, 0xE8] (fun s => s.RIP = 0x10654e) (shrR32Effect 0x10654e 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x10654e 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x10654e 0xe8 (by decide) (by decide)) pre_rip
  have f954 : InstrSpec 0x106550 [0x31, 0xC8] (fun s => s.RIP = 0x106550) (xorR32R32Effect 0x106550 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106550 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106550 0xc8 (by decide)) pre_rip
  have f955 : InstrSpec 0x106552 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x106552) (andEaxImm32Effect 0x106552 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106552 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x106552 0x5050) pre_rip
  have f956 : InstrSpec 0x106557 [0x31, 0xC1] (fun s => s.RIP = 0x106557) (xorR32R32Effect 0x106557 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106557 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106557 0xc1 (by decide)) pre_rip
  have f957 : InstrSpec 0x106559 [0x01, 0xC0] (fun s => s.RIP = 0x106559) (addR32R32Effect 0x106559 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x106559 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x106559 0xc0 (by decide)) pre_rip
  have f958 : InstrSpec 0x10655b [0x31, 0xC8] (fun s => s.RIP = 0x10655b) (xorR32R32Effect 0x10655b 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10655b 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10655b 0xc8 (by decide)) pre_rip
  have f959 : InstrSpec 0x10655d [0x66, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x10655d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10655d + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x10655d 8 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10655d 8 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m16_r16_effect_step 0x10655d 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 1872) (RestInside.out (n := 1872) f940 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1873) (ρ' := [(0, 1870), (1, 1872), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106524) f940 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1874) (RestInside.out (n := 1874) f941 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1875) (ρ' := [(0, 1874), (1, 1872), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106526) f941 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1876) (RestInside.out (n := 1876) f942 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1877) (ρ' := [(0, 1876), (1, 1872), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106528) f942 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1878) (RestInside.exec (n := 1878) (ρ' := [(0, 1876), (1, 1872), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106530) f943 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1879) (RestInside.out (n := 1879) f944 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1880) (ρ' := [(0, 1879), (1, 1872), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106538) f944 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1881) (RestInside.out (n := 1881) f945 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1882) (ρ' := [(0, 1879), (1, 1881), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10653a) f945 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1883) (RestInside.out (n := 1883) f946 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1884) (ρ' := [(0, 1879), (1, 1883), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10653d) f946 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1885) (RestInside.out (n := 1885) f947 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1886) (ρ' := [(0, 1879), (1, 1885), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10653f) f947 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1887) (RestInside.out (n := 1887) f948 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1888) (ρ' := [(0, 1879), (1, 1887), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106545) f948 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1889) (RestInside.out (n := 1889) f949 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1890) (ρ' := [(0, 1889), (1, 1887), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106547) f949 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1891) (RestInside.out (n := 1891) f950 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1892) (ρ' := [(0, 1889), (1, 1891), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10654a) f950 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1893) (RestInside.out (n := 1893) f951 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1894) (ρ' := [(0, 1889), (1, 1893), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10654c) f951 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1895) (RestInside.out (n := 1895) f952 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1896) (ρ' := [(0, 1895), (1, 1893), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10654e) f952 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1897) (RestInside.out (n := 1897) f953 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1898) (ρ' := [(0, 1897), (1, 1893), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106550) f953 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1899) (RestInside.out (n := 1899) f954 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1900) (ρ' := [(0, 1899), (1, 1893), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106552) f954 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1901) (RestInside.out (n := 1901) f955 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1902) (ρ' := [(0, 1901), (1, 1893), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106557) f955 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1903) (RestInside.out (n := 1903) f956 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1904) (ρ' := [(0, 1901), (1, 1903), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106559) f956 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1905) (RestInside.out (n := 1905) f957 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1906) (ρ' := [(0, 1905), (1, 1903), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10655b) f957 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1907) (RestInside.out (n := 1907) f958 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1908) (ρ' := [(0, 1907), (1, 1903), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10655d) f958 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1909) (RestInside.exec (n := 1909) (ρ' := [(0, 1907), (1, 1903), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106565) f959 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10593a_48 code

theorem rest_l10593a_46 [Bindings] (code : CodeMap) :
    Rest (n := 1833) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1827), (1, 1831), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      272 0x1064e2 bytes_l10593a_46 b_l10593a_46 := by
  have f920 : InstrSpec 0x1064e2 [0x89, 0xC8] (fun s => s.RIP = 0x1064e2) (movR32R32Effect 0x1064e2 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1064e2 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x1064e2 0xc8 (by decide)) pre_rip
  have f921 : InstrSpec 0x1064e4 [0xD1, 0xE8] (fun s => s.RIP = 0x1064e4) (shrR32Effect 0x1064e4 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x1064e4 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x1064e4 0xe8 (by decide) (by decide)) pre_rip
  have f922 : InstrSpec 0x1064e6 [0x31, 0xC8] (fun s => s.RIP = 0x1064e6) (xorR32R32Effect 0x1064e6 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1064e6 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1064e6 0xc8 (by decide)) pre_rip
  have f923 : InstrSpec 0x1064e8 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1064e8) (andEaxImm32Effect 0x1064e8 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x1064e8 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x1064e8 0x5050) pre_rip
  have f924 : InstrSpec 0x1064ed [0x31, 0xC1] (fun s => s.RIP = 0x1064ed) (xorR32R32Effect 0x1064ed 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1064ed 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1064ed 0xc1 (by decide)) pre_rip
  have f925 : InstrSpec 0x1064ef [0x01, 0xC0] (fun s => s.RIP = 0x1064ef) (addR32R32Effect 0x1064ef 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1064ef 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x1064ef 0xc0 (by decide)) pre_rip
  have f926 : InstrSpec 0x1064f1 [0x31, 0xC8] (fun s => s.RIP = 0x1064f1) (xorR32R32Effect 0x1064f1 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1064f1 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1064f1 0xc8 (by decide)) pre_rip
  have f927 : InstrSpec 0x1064f3 [0x66, 0x89, 0x84, 0x24, 0xC4, 0x00, 0x00, 0x00] (StorePre 0x1064f3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc4)) s (0x1064f3 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1064f3 8 0 (.sib 4 none 0 (.d32 0xc4)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1064f3 8 0 (.sib 4 none 0 (.d32 0xc4))).toInstrSpec (mov_m16_r16_effect_step 0x1064f3 0 (.sib 4 none 0 (.d32 0xc4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f928 : InstrSpec 0x1064fb [0x0F, 0xB7, 0x84, 0x24, 0xC6, 0x00, 0x00, 0x00] (LoadPre 0x1064fb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc6)) s (0x1064fb + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1064fb 8 0 (.sib 4 none 0 (.d32 0xc6)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1064fb 8 0 (.sib 4 none 0 (.d32 0xc6))).toInstrSpec (movzx_r32_m16_effect_step 0x1064fb 0 (.sib 4 none 0 (.d32 0xc6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f929 : InstrSpec 0x106503 [0x89, 0xC1] (fun s => s.RIP = 0x106503) (movR32R32Effect 0x106503 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106503 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x106503 0xc1 (by decide)) pre_rip
  have f930 : InstrSpec 0x106505 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x106505) (shrR32Effect 0x106505 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x106505 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x106505 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f931 : InstrSpec 0x106508 [0x31, 0xC1] (fun s => s.RIP = 0x106508) (xorR32R32Effect 0x106508 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106508 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106508 0xc1 (by decide)) pre_rip
  have f932 : InstrSpec 0x10650a [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x10650a) (andR32Imm32Effect 0x10650a 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10650a 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x10650a 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f933 : InstrSpec 0x106510 [0x31, 0xC8] (fun s => s.RIP = 0x106510) (xorR32R32Effect 0x106510 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106510 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106510 0xc8 (by decide)) pre_rip
  have f934 : InstrSpec 0x106512 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x106512) (shlR32Effect 0x106512 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x106512 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x106512 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f935 : InstrSpec 0x106515 [0x31, 0xC1] (fun s => s.RIP = 0x106515) (xorR32R32Effect 0x106515 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106515 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106515 0xc1 (by decide)) pre_rip
  have f936 : InstrSpec 0x106517 [0x89, 0xC8] (fun s => s.RIP = 0x106517) (movR32R32Effect 0x106517 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106517 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x106517 0xc8 (by decide)) pre_rip
  have f937 : InstrSpec 0x106519 [0xD1, 0xE8] (fun s => s.RIP = 0x106519) (shrR32Effect 0x106519 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x106519 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x106519 0xe8 (by decide) (by decide)) pre_rip
  have f938 : InstrSpec 0x10651b [0x31, 0xC8] (fun s => s.RIP = 0x10651b) (xorR32R32Effect 0x10651b 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10651b 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10651b 0xc8 (by decide)) pre_rip
  have f939 : InstrSpec 0x10651d [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x10651d) (andEaxImm32Effect 0x10651d 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x10651d 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x10651d 0x5050) pre_rip
  refine Rest.ofInside (n := 1833) (RestInside.out (n := 1833) f920 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1834) (ρ' := [(0, 1833), (1, 1831), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064e4) f920 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1835) (RestInside.out (n := 1835) f921 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1836) (ρ' := [(0, 1835), (1, 1831), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064e6) f921 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1837) (RestInside.out (n := 1837) f922 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1838) (ρ' := [(0, 1837), (1, 1831), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064e8) f922 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1839) (RestInside.out (n := 1839) f923 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1840) (ρ' := [(0, 1839), (1, 1831), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064ed) f923 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1841) (RestInside.out (n := 1841) f924 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1842) (ρ' := [(0, 1839), (1, 1841), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064ef) f924 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1843) (RestInside.out (n := 1843) f925 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1844) (ρ' := [(0, 1843), (1, 1841), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064f1) f925 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1845) (RestInside.out (n := 1845) f926 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1846) (ρ' := [(0, 1845), (1, 1841), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064f3) f926 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1847) (RestInside.exec (n := 1847) (ρ' := [(0, 1845), (1, 1841), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064fb) f927 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1848) (RestInside.out (n := 1848) f928 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1849) (ρ' := [(0, 1848), (1, 1841), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106503) f928 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1850) (RestInside.out (n := 1850) f929 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1851) (ρ' := [(0, 1848), (1, 1850), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106505) f929 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1852) (RestInside.out (n := 1852) f930 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1853) (ρ' := [(0, 1848), (1, 1852), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106508) f930 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1854) (RestInside.out (n := 1854) f931 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1855) (ρ' := [(0, 1848), (1, 1854), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10650a) f931 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1856) (RestInside.out (n := 1856) f932 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1857) (ρ' := [(0, 1848), (1, 1856), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106510) f932 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1858) (RestInside.out (n := 1858) f933 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1859) (ρ' := [(0, 1858), (1, 1856), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106512) f933 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1860) (RestInside.out (n := 1860) f934 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1861) (ρ' := [(0, 1858), (1, 1860), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106515) f934 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1862) (RestInside.out (n := 1862) f935 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1863) (ρ' := [(0, 1858), (1, 1862), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106517) f935 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1864) (RestInside.out (n := 1864) f936 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1865) (ρ' := [(0, 1864), (1, 1862), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106519) f936 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1866) (RestInside.out (n := 1866) f937 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1867) (ρ' := [(0, 1866), (1, 1862), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10651b) f937 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1868) (RestInside.out (n := 1868) f938 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1869) (ρ' := [(0, 1868), (1, 1862), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10651d) f938 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1870) (RestInside.out (n := 1870) f939 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1871) (ρ' := [(0, 1870), (1, 1862), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106522) f939 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_47 code

theorem rest_l10593a_45 [Bindings] (code : CodeMap) :
    Rest (n := 1794) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1786), (1, 1792), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      292 0x1064a0 bytes_l10593a_45 b_l10593a_45 := by
  have f900 : InstrSpec 0x1064a0 [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x1064a0) (andR32Imm32Effect 0x1064a0 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1064a0 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x1064a0 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f901 : InstrSpec 0x1064a6 [0x31, 0xC8] (fun s => s.RIP = 0x1064a6) (xorR32R32Effect 0x1064a6 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1064a6 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1064a6 0xc8 (by decide)) pre_rip
  have f902 : InstrSpec 0x1064a8 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x1064a8) (shlR32Effect 0x1064a8 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x1064a8 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x1064a8 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f903 : InstrSpec 0x1064ab [0x31, 0xC1] (fun s => s.RIP = 0x1064ab) (xorR32R32Effect 0x1064ab 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1064ab 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1064ab 0xc1 (by decide)) pre_rip
  have f904 : InstrSpec 0x1064ad [0x89, 0xC8] (fun s => s.RIP = 0x1064ad) (movR32R32Effect 0x1064ad 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1064ad 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x1064ad 0xc8 (by decide)) pre_rip
  have f905 : InstrSpec 0x1064af [0xD1, 0xE8] (fun s => s.RIP = 0x1064af) (shrR32Effect 0x1064af 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x1064af 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x1064af 0xe8 (by decide) (by decide)) pre_rip
  have f906 : InstrSpec 0x1064b1 [0x31, 0xC8] (fun s => s.RIP = 0x1064b1) (xorR32R32Effect 0x1064b1 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1064b1 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1064b1 0xc8 (by decide)) pre_rip
  have f907 : InstrSpec 0x1064b3 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1064b3) (andEaxImm32Effect 0x1064b3 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x1064b3 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x1064b3 0x5050) pre_rip
  have f908 : InstrSpec 0x1064b8 [0x31, 0xC1] (fun s => s.RIP = 0x1064b8) (xorR32R32Effect 0x1064b8 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1064b8 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1064b8 0xc1 (by decide)) pre_rip
  have f909 : InstrSpec 0x1064ba [0x01, 0xC0] (fun s => s.RIP = 0x1064ba) (addR32R32Effect 0x1064ba 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1064ba 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x1064ba 0xc0 (by decide)) pre_rip
  have f910 : InstrSpec 0x1064bc [0x31, 0xC8] (fun s => s.RIP = 0x1064bc) (xorR32R32Effect 0x1064bc 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1064bc 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1064bc 0xc8 (by decide)) pre_rip
  have f911 : InstrSpec 0x1064be [0x66, 0x89, 0x84, 0x24, 0xC2, 0x00, 0x00, 0x00] (StorePre 0x1064be 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc2)) s (0x1064be + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1064be 8 0 (.sib 4 none 0 (.d32 0xc2)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1064be 8 0 (.sib 4 none 0 (.d32 0xc2))).toInstrSpec (mov_m16_r16_effect_step 0x1064be 0 (.sib 4 none 0 (.d32 0xc2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f912 : InstrSpec 0x1064c6 [0x0F, 0xB7, 0x84, 0x24, 0xC4, 0x00, 0x00, 0x00] (LoadPre 0x1064c6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc4)) s (0x1064c6 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1064c6 8 0 (.sib 4 none 0 (.d32 0xc4)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1064c6 8 0 (.sib 4 none 0 (.d32 0xc4))).toInstrSpec (movzx_r32_m16_effect_step 0x1064c6 0 (.sib 4 none 0 (.d32 0xc4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f913 : InstrSpec 0x1064ce [0x89, 0xC1] (fun s => s.RIP = 0x1064ce) (movR32R32Effect 0x1064ce 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1064ce 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1064ce 0xc1 (by decide)) pre_rip
  have f914 : InstrSpec 0x1064d0 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x1064d0) (shrR32Effect 0x1064d0 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1064d0 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x1064d0 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f915 : InstrSpec 0x1064d3 [0x31, 0xC1] (fun s => s.RIP = 0x1064d3) (xorR32R32Effect 0x1064d3 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1064d3 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1064d3 0xc1 (by decide)) pre_rip
  have f916 : InstrSpec 0x1064d5 [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x1064d5) (andR32Imm32Effect 0x1064d5 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1064d5 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x1064d5 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f917 : InstrSpec 0x1064db [0x31, 0xC8] (fun s => s.RIP = 0x1064db) (xorR32R32Effect 0x1064db 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1064db 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1064db 0xc8 (by decide)) pre_rip
  have f918 : InstrSpec 0x1064dd [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x1064dd) (shlR32Effect 0x1064dd 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x1064dd 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x1064dd 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f919 : InstrSpec 0x1064e0 [0x31, 0xC1] (fun s => s.RIP = 0x1064e0) (xorR32R32Effect 0x1064e0 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1064e0 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1064e0 0xc1 (by decide)) pre_rip
  refine Rest.ofInside (n := 1794) (RestInside.out (n := 1794) f900 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1795) (ρ' := [(0, 1786), (1, 1794), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064a6) f900 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1796) (RestInside.out (n := 1796) f901 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1797) (ρ' := [(0, 1796), (1, 1794), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064a8) f901 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1798) (RestInside.out (n := 1798) f902 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1799) (ρ' := [(0, 1796), (1, 1798), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064ab) f902 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1800) (RestInside.out (n := 1800) f903 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1801) (ρ' := [(0, 1796), (1, 1800), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064ad) f903 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1802) (RestInside.out (n := 1802) f904 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1803) (ρ' := [(0, 1802), (1, 1800), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064af) f904 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1804) (RestInside.out (n := 1804) f905 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1805) (ρ' := [(0, 1804), (1, 1800), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064b1) f905 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1806) (RestInside.out (n := 1806) f906 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1807) (ρ' := [(0, 1806), (1, 1800), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064b3) f906 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1808) (RestInside.out (n := 1808) f907 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1809) (ρ' := [(0, 1808), (1, 1800), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064b8) f907 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1810) (RestInside.out (n := 1810) f908 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1811) (ρ' := [(0, 1808), (1, 1810), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064ba) f908 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1812) (RestInside.out (n := 1812) f909 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1813) (ρ' := [(0, 1812), (1, 1810), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064bc) f909 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1814) (RestInside.out (n := 1814) f910 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1815) (ρ' := [(0, 1814), (1, 1810), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064be) f910 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1816) (RestInside.exec (n := 1816) (ρ' := [(0, 1814), (1, 1810), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064c6) f911 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1817) (RestInside.out (n := 1817) f912 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1818) (ρ' := [(0, 1817), (1, 1810), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064ce) f912 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1819) (RestInside.out (n := 1819) f913 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1820) (ρ' := [(0, 1817), (1, 1819), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064d0) f913 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1821) (RestInside.out (n := 1821) f914 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1822) (ρ' := [(0, 1817), (1, 1821), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064d3) f914 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1823) (RestInside.out (n := 1823) f915 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1824) (ρ' := [(0, 1817), (1, 1823), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064d5) f915 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1825) (RestInside.out (n := 1825) f916 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1826) (ρ' := [(0, 1817), (1, 1825), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064db) f916 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1827) (RestInside.out (n := 1827) f917 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1828) (ρ' := [(0, 1827), (1, 1825), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064dd) f917 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1829) (RestInside.out (n := 1829) f918 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1830) (ρ' := [(0, 1827), (1, 1829), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064e0) f918 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1831) (RestInside.out (n := 1831) f919 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1832) (ρ' := [(0, 1827), (1, 1831), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064e2) f919 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_46 code

theorem rest_l10593a_44 [Bindings] (code : CodeMap) :
    Rest (n := 1755) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1752), (1, 1748), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      312 0x10645c bytes_l10593a_44 b_l10593a_44 := by
  have f880 : InstrSpec 0x10645c [0x0F, 0xB7, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x10645c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10645c + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x10645c 8 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10645c 8 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (movzx_r32_m16_effect_step 0x10645c 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f881 : InstrSpec 0x106464 [0x89, 0xC1] (fun s => s.RIP = 0x106464) (movR32R32Effect 0x106464 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106464 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x106464 0xc1 (by decide)) pre_rip
  have f882 : InstrSpec 0x106466 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x106466) (shrR32Effect 0x106466 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x106466 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x106466 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f883 : InstrSpec 0x106469 [0x31, 0xC1] (fun s => s.RIP = 0x106469) (xorR32R32Effect 0x106469 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106469 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106469 0xc1 (by decide)) pre_rip
  have f884 : InstrSpec 0x10646b [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x10646b) (andR32Imm32Effect 0x10646b 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10646b 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x10646b 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f885 : InstrSpec 0x106471 [0x31, 0xC8] (fun s => s.RIP = 0x106471) (xorR32R32Effect 0x106471 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106471 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106471 0xc8 (by decide)) pre_rip
  have f886 : InstrSpec 0x106473 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x106473) (shlR32Effect 0x106473 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x106473 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x106473 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f887 : InstrSpec 0x106476 [0x31, 0xC1] (fun s => s.RIP = 0x106476) (xorR32R32Effect 0x106476 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106476 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106476 0xc1 (by decide)) pre_rip
  have f888 : InstrSpec 0x106478 [0x89, 0xC8] (fun s => s.RIP = 0x106478) (movR32R32Effect 0x106478 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106478 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x106478 0xc8 (by decide)) pre_rip
  have f889 : InstrSpec 0x10647a [0xD1, 0xE8] (fun s => s.RIP = 0x10647a) (shrR32Effect 0x10647a 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x10647a 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x10647a 0xe8 (by decide) (by decide)) pre_rip
  have f890 : InstrSpec 0x10647c [0x31, 0xC8] (fun s => s.RIP = 0x10647c) (xorR32R32Effect 0x10647c 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10647c 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10647c 0xc8 (by decide)) pre_rip
  have f891 : InstrSpec 0x10647e [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x10647e) (andEaxImm32Effect 0x10647e 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x10647e 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x10647e 0x5050) pre_rip
  have f892 : InstrSpec 0x106483 [0x31, 0xC1] (fun s => s.RIP = 0x106483) (xorR32R32Effect 0x106483 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106483 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106483 0xc1 (by decide)) pre_rip
  have f893 : InstrSpec 0x106485 [0x01, 0xC0] (fun s => s.RIP = 0x106485) (addR32R32Effect 0x106485 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x106485 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x106485 0xc0 (by decide)) pre_rip
  have f894 : InstrSpec 0x106487 [0x31, 0xC8] (fun s => s.RIP = 0x106487) (xorR32R32Effect 0x106487 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106487 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106487 0xc8 (by decide)) pre_rip
  have f895 : InstrSpec 0x106489 [0x66, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x106489 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x106489 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106489 8 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106489 8 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m16_r16_effect_step 0x106489 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f896 : InstrSpec 0x106491 [0x0F, 0xB7, 0x84, 0x24, 0xC2, 0x00, 0x00, 0x00] (LoadPre 0x106491 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc2)) s (0x106491 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106491 8 0 (.sib 4 none 0 (.d32 0xc2)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106491 8 0 (.sib 4 none 0 (.d32 0xc2))).toInstrSpec (movzx_r32_m16_effect_step 0x106491 0 (.sib 4 none 0 (.d32 0xc2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f897 : InstrSpec 0x106499 [0x89, 0xC1] (fun s => s.RIP = 0x106499) (movR32R32Effect 0x106499 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106499 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x106499 0xc1 (by decide)) pre_rip
  have f898 : InstrSpec 0x10649b [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x10649b) (shrR32Effect 0x10649b 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10649b 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x10649b 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f899 : InstrSpec 0x10649e [0x31, 0xC1] (fun s => s.RIP = 0x10649e) (xorR32R32Effect 0x10649e 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10649e 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10649e 0xc1 (by decide)) pre_rip
  refine Rest.ofInside (n := 1755) (RestInside.out (n := 1755) f880 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1756) (ρ' := [(0, 1755), (1, 1748), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106464) f880 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1757) (RestInside.out (n := 1757) f881 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1758) (ρ' := [(0, 1755), (1, 1757), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106466) f881 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1759) (RestInside.out (n := 1759) f882 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1760) (ρ' := [(0, 1755), (1, 1759), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106469) f882 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1761) (RestInside.out (n := 1761) f883 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1762) (ρ' := [(0, 1755), (1, 1761), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10646b) f883 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1763) (RestInside.out (n := 1763) f884 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1764) (ρ' := [(0, 1755), (1, 1763), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106471) f884 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1765) (RestInside.out (n := 1765) f885 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1766) (ρ' := [(0, 1765), (1, 1763), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106473) f885 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1767) (RestInside.out (n := 1767) f886 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1768) (ρ' := [(0, 1765), (1, 1767), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106476) f886 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1769) (RestInside.out (n := 1769) f887 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1770) (ρ' := [(0, 1765), (1, 1769), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106478) f887 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1771) (RestInside.out (n := 1771) f888 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1772) (ρ' := [(0, 1771), (1, 1769), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10647a) f888 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1773) (RestInside.out (n := 1773) f889 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1774) (ρ' := [(0, 1773), (1, 1769), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10647c) f889 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1775) (RestInside.out (n := 1775) f890 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1776) (ρ' := [(0, 1775), (1, 1769), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10647e) f890 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1777) (RestInside.out (n := 1777) f891 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1778) (ρ' := [(0, 1777), (1, 1769), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106483) f891 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1779) (RestInside.out (n := 1779) f892 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1780) (ρ' := [(0, 1777), (1, 1779), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106485) f892 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1781) (RestInside.out (n := 1781) f893 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1782) (ρ' := [(0, 1781), (1, 1779), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106487) f893 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1783) (RestInside.out (n := 1783) f894 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1784) (ρ' := [(0, 1783), (1, 1779), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106489) f894 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1785) (RestInside.exec (n := 1785) (ρ' := [(0, 1783), (1, 1779), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106491) f895 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1786) (RestInside.out (n := 1786) f896 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1787) (ρ' := [(0, 1786), (1, 1779), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106499) f896 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1788) (RestInside.out (n := 1788) f897 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1789) (ρ' := [(0, 1786), (1, 1788), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10649b) f897 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1790) (RestInside.out (n := 1790) f898 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1791) (ρ' := [(0, 1786), (1, 1790), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10649e) f898 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1792) (RestInside.out (n := 1792) f899 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1793) (ρ' := [(0, 1786), (1, 1792), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1064a0) f899 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_45 code

theorem rest_l10593a_43 [Bindings] (code : CodeMap) :
    Rest (n := 1716) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1704), (1, 1708), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1714), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      332 0x106417 bytes_l10593a_43 b_l10593a_43 := by
  have f860 : InstrSpec 0x106417 [0x41, 0x81, 0xE2, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x106417) (andR32Imm32Effect 0x106417 7 10 0x5050)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106417 7 10 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x106417 0x41 0xe2 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f861 : InstrSpec 0x10641e [0x44, 0x31, 0xD1] (fun s => s.RIP = 0x10641e) (xorR32R32Effect 0x10641e 3 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10641e 3 1 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x10641e 0x44 0xd1 (by decide) (by decide)) pre_rip
  have f862 : InstrSpec 0x106421 [0x45, 0x01, 0xD2] (fun s => s.RIP = 0x106421) (addR32R32Effect 0x106421 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x106421 3 10 10).toInstrSpec (add_r32_r32_rex_effect_step 0x106421 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f863 : InstrSpec 0x106424 [0x41, 0x31, 0xCA] (fun s => s.RIP = 0x106424) (xorR32R32Effect 0x106424 3 10 1)
      [.gpr 10, .gpr 1] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106424 3 10 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x106424 0x41 0xca (by decide) (by decide)) pre_rip
  have f864 : InstrSpec 0x106427 [0x0F, 0xB7, 0x84, 0x24, 0xBE, 0x00, 0x00, 0x00] (LoadPre 0x106427 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbe)) s (0x106427 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106427 8 0 (.sib 4 none 0 (.d32 0xbe)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106427 8 0 (.sib 4 none 0 (.d32 0xbe))).toInstrSpec (movzx_r32_m16_effect_step 0x106427 0 (.sib 4 none 0 (.d32 0xbe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f865 : InstrSpec 0x10642f [0x89, 0xC1] (fun s => s.RIP = 0x10642f) (movR32R32Effect 0x10642f 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10642f 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x10642f 0xc1 (by decide)) pre_rip
  have f866 : InstrSpec 0x106431 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x106431) (shrR32Effect 0x106431 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x106431 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x106431 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f867 : InstrSpec 0x106434 [0x31, 0xC1] (fun s => s.RIP = 0x106434) (xorR32R32Effect 0x106434 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106434 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106434 0xc1 (by decide)) pre_rip
  have f868 : InstrSpec 0x106436 [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x106436) (andR32Imm32Effect 0x106436 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106436 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x106436 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f869 : InstrSpec 0x10643c [0x31, 0xC8] (fun s => s.RIP = 0x10643c) (xorR32R32Effect 0x10643c 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10643c 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10643c 0xc8 (by decide)) pre_rip
  have f870 : InstrSpec 0x10643e [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x10643e) (shlR32Effect 0x10643e 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10643e 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x10643e 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f871 : InstrSpec 0x106441 [0x31, 0xC1] (fun s => s.RIP = 0x106441) (xorR32R32Effect 0x106441 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106441 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106441 0xc1 (by decide)) pre_rip
  have f872 : InstrSpec 0x106443 [0x89, 0xC8] (fun s => s.RIP = 0x106443) (movR32R32Effect 0x106443 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106443 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x106443 0xc8 (by decide)) pre_rip
  have f873 : InstrSpec 0x106445 [0xD1, 0xE8] (fun s => s.RIP = 0x106445) (shrR32Effect 0x106445 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x106445 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x106445 0xe8 (by decide) (by decide)) pre_rip
  have f874 : InstrSpec 0x106447 [0x31, 0xC8] (fun s => s.RIP = 0x106447) (xorR32R32Effect 0x106447 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106447 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106447 0xc8 (by decide)) pre_rip
  have f875 : InstrSpec 0x106449 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x106449) (andEaxImm32Effect 0x106449 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106449 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x106449 0x5050) pre_rip
  have f876 : InstrSpec 0x10644e [0x31, 0xC1] (fun s => s.RIP = 0x10644e) (xorR32R32Effect 0x10644e 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10644e 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10644e 0xc1 (by decide)) pre_rip
  have f877 : InstrSpec 0x106450 [0x01, 0xC0] (fun s => s.RIP = 0x106450) (addR32R32Effect 0x106450 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x106450 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x106450 0xc0 (by decide)) pre_rip
  have f878 : InstrSpec 0x106452 [0x31, 0xC8] (fun s => s.RIP = 0x106452) (xorR32R32Effect 0x106452 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106452 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106452 0xc8 (by decide)) pre_rip
  have f879 : InstrSpec 0x106454 [0x66, 0x89, 0x84, 0x24, 0xBE, 0x00, 0x00, 0x00] (StorePre 0x106454 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbe)) s (0x106454 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106454 8 0 (.sib 4 none 0 (.d32 0xbe)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106454 8 0 (.sib 4 none 0 (.d32 0xbe))).toInstrSpec (mov_m16_r16_effect_step 0x106454 0 (.sib 4 none 0 (.d32 0xbe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 1716) (RestInside.out (n := 1716) f860 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1717) (ρ' := [(0, 1704), (1, 1708), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1716), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10641e) f860 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1718) (RestInside.out (n := 1718) f861 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1719) (ρ' := [(0, 1704), (1, 1718), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1716), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106421) f861 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1720) (RestInside.out (n := 1720) f862 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1721) (ρ' := [(0, 1704), (1, 1718), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1720), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106424) f862 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1722) (RestInside.out (n := 1722) f863 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1723) (ρ' := [(0, 1704), (1, 1718), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106427) f863 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1724) (RestInside.out (n := 1724) f864 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1725) (ρ' := [(0, 1724), (1, 1718), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10642f) f864 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1726) (RestInside.out (n := 1726) f865 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1727) (ρ' := [(0, 1724), (1, 1726), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106431) f865 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1728) (RestInside.out (n := 1728) f866 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1729) (ρ' := [(0, 1724), (1, 1728), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106434) f866 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1730) (RestInside.out (n := 1730) f867 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1731) (ρ' := [(0, 1724), (1, 1730), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106436) f867 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1732) (RestInside.out (n := 1732) f868 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1733) (ρ' := [(0, 1724), (1, 1732), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10643c) f868 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1734) (RestInside.out (n := 1734) f869 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1735) (ρ' := [(0, 1734), (1, 1732), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10643e) f869 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1736) (RestInside.out (n := 1736) f870 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1737) (ρ' := [(0, 1734), (1, 1736), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106441) f870 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1738) (RestInside.out (n := 1738) f871 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1739) (ρ' := [(0, 1734), (1, 1738), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106443) f871 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1740) (RestInside.out (n := 1740) f872 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1741) (ρ' := [(0, 1740), (1, 1738), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106445) f872 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1742) (RestInside.out (n := 1742) f873 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1743) (ρ' := [(0, 1742), (1, 1738), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106447) f873 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1744) (RestInside.out (n := 1744) f874 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1745) (ρ' := [(0, 1744), (1, 1738), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106449) f874 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1746) (RestInside.out (n := 1746) f875 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1747) (ρ' := [(0, 1746), (1, 1738), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10644e) f875 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1748) (RestInside.out (n := 1748) f876 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1749) (ρ' := [(0, 1746), (1, 1748), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106450) f876 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1750) (RestInside.out (n := 1750) f877 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1751) (ρ' := [(0, 1750), (1, 1748), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106452) f877 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1752) (RestInside.out (n := 1752) f878 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1753) (ρ' := [(0, 1752), (1, 1748), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106454) f878 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1754) (RestInside.exec (n := 1754) (ρ' := [(0, 1752), (1, 1748), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1722), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10645c) f879 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10593a_44 code

theorem rest_l10593a_42 [Bindings] (code : CodeMap) :
    Rest (n := 1677) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1671), (1, 1642), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      352 0x1063ce bytes_l10593a_42 b_l10593a_42 := by
  have f840 : InstrSpec 0x1063ce [0x0F, 0xB7, 0x84, 0x24, 0xBA, 0x00, 0x00, 0x00] (LoadPre 0x1063ce (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xba)) s (0x1063ce + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1063ce 8 0 (.sib 4 none 0 (.d32 0xba)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1063ce 8 0 (.sib 4 none 0 (.d32 0xba))).toInstrSpec (movzx_r32_m16_effect_step 0x1063ce 0 (.sib 4 none 0 (.d32 0xba)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f841 : InstrSpec 0x1063d6 [0x89, 0xC1] (fun s => s.RIP = 0x1063d6) (movR32R32Effect 0x1063d6 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1063d6 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1063d6 0xc1 (by decide)) pre_rip
  have f842 : InstrSpec 0x1063d8 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x1063d8) (shrR32Effect 0x1063d8 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1063d8 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x1063d8 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f843 : InstrSpec 0x1063db [0x31, 0xC1] (fun s => s.RIP = 0x1063db) (xorR32R32Effect 0x1063db 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1063db 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1063db 0xc1 (by decide)) pre_rip
  have f844 : InstrSpec 0x1063dd [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x1063dd) (andR32Imm32Effect 0x1063dd 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1063dd 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x1063dd 0xe1 0x3030 (by decide) (by decide)) pre_rip
  have f845 : InstrSpec 0x1063e3 [0x31, 0xC8] (fun s => s.RIP = 0x1063e3) (xorR32R32Effect 0x1063e3 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1063e3 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1063e3 0xc8 (by decide)) pre_rip
  have f846 : InstrSpec 0x1063e5 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x1063e5) (shlR32Effect 0x1063e5 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x1063e5 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x1063e5 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f847 : InstrSpec 0x1063e8 [0x31, 0xC1] (fun s => s.RIP = 0x1063e8) (xorR32R32Effect 0x1063e8 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1063e8 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1063e8 0xc1 (by decide)) pre_rip
  have f848 : InstrSpec 0x1063ea [0x66, 0x89, 0x8C, 0x24, 0xBA, 0x00, 0x00, 0x00] (StorePre 0x1063ea 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xba)) s (0x1063ea + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1063ea 8 1 (.sib 4 none 0 (.d32 0xba)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1063ea 8 1 (.sib 4 none 0 (.d32 0xba))).toInstrSpec (mov_m16_r16_effect_step 0x1063ea 1 (.sib 4 none 0 (.d32 0xba)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f849 : InstrSpec 0x1063f2 [0x0F, 0xB7, 0x84, 0x24, 0xBC, 0x00, 0x00, 0x00] (LoadPre 0x1063f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbc)) s (0x1063f2 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1063f2 8 0 (.sib 4 none 0 (.d32 0xbc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1063f2 8 0 (.sib 4 none 0 (.d32 0xbc))).toInstrSpec (movzx_r32_m16_effect_step 0x1063f2 0 (.sib 4 none 0 (.d32 0xbc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f850 : InstrSpec 0x1063fa [0x89, 0xC1] (fun s => s.RIP = 0x1063fa) (movR32R32Effect 0x1063fa 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1063fa 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1063fa 0xc1 (by decide)) pre_rip
  have f851 : InstrSpec 0x1063fc [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x1063fc) (shrR32Effect 0x1063fc 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1063fc 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x1063fc 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f852 : InstrSpec 0x1063ff [0x31, 0xC1] (fun s => s.RIP = 0x1063ff) (xorR32R32Effect 0x1063ff 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1063ff 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1063ff 0xc1 (by decide)) pre_rip
  have f853 : InstrSpec 0x106401 [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x106401) (andR32Imm32Effect 0x106401 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106401 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x106401 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f854 : InstrSpec 0x106407 [0x31, 0xC8] (fun s => s.RIP = 0x106407) (xorR32R32Effect 0x106407 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106407 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106407 0xc8 (by decide)) pre_rip
  have f855 : InstrSpec 0x106409 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x106409) (shlR32Effect 0x106409 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x106409 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x106409 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f856 : InstrSpec 0x10640c [0x31, 0xC1] (fun s => s.RIP = 0x10640c) (xorR32R32Effect 0x10640c 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10640c 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10640c 0xc1 (by decide)) pre_rip
  have f857 : InstrSpec 0x10640e [0x41, 0x89, 0xCA] (fun s => s.RIP = 0x10640e) (movR32R32Effect 0x10640e 3 10 1)
      [.gpr 1] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x10640e 3 10 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x10640e 0x41 0xca (by decide) (by decide)) pre_rip
  have f858 : InstrSpec 0x106411 [0x41, 0xD1, 0xEA] (fun s => s.RIP = 0x106411) (shrR32Effect 0x106411 3 10 1)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x106411 3 10 1).toInstrSpec (shr_r32_one_rex_effect_step 0x106411 0x41 0xea (by decide) (by decide) (by decide)) pre_rip
  have f859 : InstrSpec 0x106414 [0x41, 0x31, 0xCA] (fun s => s.RIP = 0x106414) (xorR32R32Effect 0x106414 3 10 1)
      [.gpr 10, .gpr 1] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106414 3 10 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x106414 0x41 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1677) (RestInside.out (n := 1677) f840 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1678) (ρ' := [(0, 1677), (1, 1642), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063d6) f840 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1679) (RestInside.out (n := 1679) f841 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1680) (ρ' := [(0, 1677), (1, 1679), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063d8) f841 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1681) (RestInside.out (n := 1681) f842 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1682) (ρ' := [(0, 1677), (1, 1681), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063db) f842 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1683) (RestInside.out (n := 1683) f843 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1684) (ρ' := [(0, 1677), (1, 1683), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063dd) f843 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1685) (RestInside.out (n := 1685) f844 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1686) (ρ' := [(0, 1677), (1, 1685), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063e3) f844 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1687) (RestInside.out (n := 1687) f845 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1688) (ρ' := [(0, 1687), (1, 1685), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063e5) f845 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1689) (RestInside.out (n := 1689) f846 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1690) (ρ' := [(0, 1687), (1, 1689), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063e8) f846 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1691) (RestInside.out (n := 1691) f847 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1692) (ρ' := [(0, 1687), (1, 1691), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063ea) f847 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1693) (RestInside.exec (n := 1693) (ρ' := [(0, 1687), (1, 1691), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063f2) f848 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1694) (RestInside.out (n := 1694) f849 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1695) (ρ' := [(0, 1694), (1, 1691), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063fa) f849 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1696) (RestInside.out (n := 1696) f850 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1697) (ρ' := [(0, 1694), (1, 1696), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063fc) f850 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1698) (RestInside.out (n := 1698) f851 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1699) (ρ' := [(0, 1694), (1, 1698), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063ff) f851 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1700) (RestInside.out (n := 1700) f852 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1701) (ρ' := [(0, 1694), (1, 1700), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106401) f852 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1702) (RestInside.out (n := 1702) f853 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1703) (ρ' := [(0, 1694), (1, 1702), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106407) f853 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1704) (RestInside.out (n := 1704) f854 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1705) (ρ' := [(0, 1704), (1, 1702), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106409) f854 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1706) (RestInside.out (n := 1706) f855 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1707) (ρ' := [(0, 1704), (1, 1706), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10640c) f855 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1708) (RestInside.out (n := 1708) f856 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1709) (ρ' := [(0, 1704), (1, 1708), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10640e) f856 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1710) (RestInside.out (n := 1710) f857 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1711) (ρ' := [(0, 1704), (1, 1708), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1710), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106411) f857 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1712) (RestInside.out (n := 1712) f858 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1713) (ρ' := [(0, 1704), (1, 1708), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1712), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106414) f858 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1714) (RestInside.out (n := 1714) f859 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1715) (ρ' := [(0, 1704), (1, 1708), (3, 1659), (4, 4), (5, 1592), (9, 1033), (10, 1714), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106417) f859 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_43 code

theorem rest_l10593a_41 [Bindings] (code : CodeMap) :
    Rest (n := 1638) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1628), (1, 1636), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      372 0x106380 bytes_l10593a_41 b_l10593a_41 := by
  have f820 : InstrSpec 0x106380 [0x31, 0xC8] (fun s => s.RIP = 0x106380) (xorR32R32Effect 0x106380 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106380 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106380 0xc8 (by decide)) pre_rip
  have f821 : InstrSpec 0x106382 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x106382) (shlR32Effect 0x106382 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x106382 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x106382 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f822 : InstrSpec 0x106385 [0x31, 0xC1] (fun s => s.RIP = 0x106385) (xorR32R32Effect 0x106385 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106385 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106385 0xc1 (by decide)) pre_rip
  have f823 : InstrSpec 0x106387 [0x66, 0x89, 0x8C, 0x24, 0xB4, 0x00, 0x00, 0x00] (StorePre 0x106387 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x106387 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106387 8 1 (.sib 4 none 0 (.d32 0xb4)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106387 8 1 (.sib 4 none 0 (.d32 0xb4))).toInstrSpec (mov_m16_r16_effect_step 0x106387 1 (.sib 4 none 0 (.d32 0xb4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f824 : InstrSpec 0x10638f [0x0F, 0xB7, 0x84, 0x24, 0xB6, 0x00, 0x00, 0x00] (LoadPre 0x10638f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb6)) s (0x10638f + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x10638f 8 0 (.sib 4 none 0 (.d32 0xb6)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10638f 8 0 (.sib 4 none 0 (.d32 0xb6))).toInstrSpec (movzx_r32_m16_effect_step 0x10638f 0 (.sib 4 none 0 (.d32 0xb6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f825 : InstrSpec 0x106397 [0x89, 0xC3] (fun s => s.RIP = 0x106397) (movR32R32Effect 0x106397 2 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x106397 2 3 0).toInstrSpec (mov_r32_r32_effect_step 0x106397 0xc3 (by decide)) pre_rip
  have f826 : InstrSpec 0x106399 [0xC1, 0xEB, 0x02] (fun s => s.RIP = 0x106399) (shrR32Effect 0x106399 3 3 2)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR32Effect_footprint 0x106399 3 3 2).toInstrSpec (shr_r32_imm8_effect_step 0x106399 0xeb 0x2 (by decide) (by decide)) pre_rip
  have f827 : InstrSpec 0x10639c [0x31, 0xC3] (fun s => s.RIP = 0x10639c) (xorR32R32Effect 0x10639c 2 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10639c 2 3 0).toInstrSpec (xor_r32_r32_effect_step 0x10639c 0xc3 (by decide)) pre_rip
  have f828 : InstrSpec 0x10639e [0x81, 0xE3, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x10639e) (andR32Imm32Effect 0x10639e 6 3 0x3030)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10639e 6 3 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x10639e 0xe3 0x3030 (by decide) (by decide)) pre_rip
  have f829 : InstrSpec 0x1063a4 [0x31, 0xD8] (fun s => s.RIP = 0x1063a4) (xorR32R32Effect 0x1063a4 2 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1063a4 2 0 3).toInstrSpec (xor_r32_r32_effect_step 0x1063a4 0xd8 (by decide)) pre_rip
  have f830 : InstrSpec 0x1063a6 [0xC1, 0xE3, 0x02] (fun s => s.RIP = 0x1063a6) (shlR32Effect 0x1063a6 3 3 2)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shlR32Effect_footprint 0x1063a6 3 3 2).toInstrSpec (shl_r32_imm8_effect_step 0x1063a6 0xe3 0x2 (by decide) (by decide)) pre_rip
  have f831 : InstrSpec 0x1063a9 [0x31, 0xC3] (fun s => s.RIP = 0x1063a9) (xorR32R32Effect 0x1063a9 2 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1063a9 2 3 0).toInstrSpec (xor_r32_r32_effect_step 0x1063a9 0xc3 (by decide)) pre_rip
  have f832 : InstrSpec 0x1063ab [0x0F, 0xB7, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x1063ab (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1063ab + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1063ab 8 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1063ab 8 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (movzx_r32_m16_effect_step 0x1063ab 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f833 : InstrSpec 0x1063b3 [0x41, 0x89, 0xC3] (fun s => s.RIP = 0x1063b3) (movR32R32Effect 0x1063b3 3 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x1063b3 3 11 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x1063b3 0x41 0xc3 (by decide) (by decide)) pre_rip
  have f834 : InstrSpec 0x1063b6 [0x41, 0xC1, 0xEB, 0x02] (fun s => s.RIP = 0x1063b6) (shrR32Effect 0x1063b6 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x1063b6 4 11 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x1063b6 0x41 0xeb 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f835 : InstrSpec 0x1063ba [0x41, 0x31, 0xC3] (fun s => s.RIP = 0x1063ba) (xorR32R32Effect 0x1063ba 3 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1063ba 3 11 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x1063ba 0x41 0xc3 (by decide) (by decide)) pre_rip
  have f836 : InstrSpec 0x1063bd [0x41, 0x81, 0xE3, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x1063bd) (andR32Imm32Effect 0x1063bd 7 11 0x3030)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1063bd 7 11 0x3030).toInstrSpec (and_r32_imm32_rex_effect_step 0x1063bd 0x41 0xe3 0x3030 (by decide) (by decide) (by decide)) pre_rip
  have f837 : InstrSpec 0x1063c4 [0x44, 0x31, 0xD8] (fun s => s.RIP = 0x1063c4) (xorR32R32Effect 0x1063c4 3 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1063c4 3 0 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x1063c4 0x44 0xd8 (by decide) (by decide)) pre_rip
  have f838 : InstrSpec 0x1063c7 [0x41, 0xC1, 0xE3, 0x02] (fun s => s.RIP = 0x1063c7) (shlR32Effect 0x1063c7 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR32Effect_footprint 0x1063c7 4 11 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1063c7 0x41 0xe3 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f839 : InstrSpec 0x1063cb [0x41, 0x31, 0xC3] (fun s => s.RIP = 0x1063cb) (xorR32R32Effect 0x1063cb 3 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1063cb 3 11 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x1063cb 0x41 0xc3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1638) (RestInside.out (n := 1638) f820 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1639) (ρ' := [(0, 1638), (1, 1636), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106382) f820 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1640) (RestInside.out (n := 1640) f821 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1641) (ρ' := [(0, 1638), (1, 1640), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106385) f821 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1642) (RestInside.out (n := 1642) f822 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1643) (ρ' := [(0, 1638), (1, 1642), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106387) f822 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1644) (RestInside.exec (n := 1644) (ρ' := [(0, 1638), (1, 1642), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10638f) f823 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1645) (RestInside.out (n := 1645) f824 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1646) (ρ' := [(0, 1645), (1, 1642), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106397) f824 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1647) (RestInside.out (n := 1647) f825 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1648) (ρ' := [(0, 1645), (1, 1642), (3, 1647), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106399) f825 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1649) (RestInside.out (n := 1649) f826 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1650) (ρ' := [(0, 1645), (1, 1642), (3, 1649), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10639c) f826 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1651) (RestInside.out (n := 1651) f827 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1652) (ρ' := [(0, 1645), (1, 1642), (3, 1651), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10639e) f827 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1653) (RestInside.out (n := 1653) f828 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1654) (ρ' := [(0, 1645), (1, 1642), (3, 1653), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063a4) f828 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1655) (RestInside.out (n := 1655) f829 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1656) (ρ' := [(0, 1655), (1, 1642), (3, 1653), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063a6) f829 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1657) (RestInside.out (n := 1657) f830 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1658) (ρ' := [(0, 1655), (1, 1642), (3, 1657), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063a9) f830 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1659) (RestInside.out (n := 1659) f831 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1660) (ρ' := [(0, 1655), (1, 1642), (3, 1659), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063ab) f831 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1661) (RestInside.out (n := 1661) f832 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1662) (ρ' := [(0, 1661), (1, 1642), (3, 1659), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063b3) f832 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1663) (RestInside.out (n := 1663) f833 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1664) (ρ' := [(0, 1661), (1, 1642), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1663), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063b6) f833 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1665) (RestInside.out (n := 1665) f834 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1666) (ρ' := [(0, 1661), (1, 1642), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1665), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063ba) f834 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1667) (RestInside.out (n := 1667) f835 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1668) (ρ' := [(0, 1661), (1, 1642), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1667), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063bd) f835 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1669) (RestInside.out (n := 1669) f836 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1670) (ρ' := [(0, 1661), (1, 1642), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1669), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063c4) f836 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1671) (RestInside.out (n := 1671) f837 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1672) (ρ' := [(0, 1671), (1, 1642), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1669), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063c7) f837 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1673) (RestInside.out (n := 1673) f838 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1674) (ρ' := [(0, 1671), (1, 1642), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1673), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063cb) f838 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1675) (RestInside.out (n := 1675) f839 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1676) (ρ' := [(0, 1671), (1, 1642), (3, 1659), (4, 4), (5, 1592), (9, 1033), (11, 1675), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1063ce) f839 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_42 code

theorem rest_l10593a_40 [Bindings] (code : CodeMap) :
    Rest (n := 1600) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1594), (1, 1598), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      392 0x106330 bytes_l10593a_40 b_l10593a_40 := by
  have f800 : InstrSpec 0x106330 [0x31, 0xC1] (fun s => s.RIP = 0x106330) (xorR32R32Effect 0x106330 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106330 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106330 0xc1 (by decide)) pre_rip
  have f801 : InstrSpec 0x106332 [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x106332) (andR32Imm32Effect 0x106332 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106332 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x106332 0xe1 0x3030 (by decide) (by decide)) pre_rip
  have f802 : InstrSpec 0x106338 [0x31, 0xC8] (fun s => s.RIP = 0x106338) (xorR32R32Effect 0x106338 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106338 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106338 0xc8 (by decide)) pre_rip
  have f803 : InstrSpec 0x10633a [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x10633a) (shlR32Effect 0x10633a 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10633a 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x10633a 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f804 : InstrSpec 0x10633d [0x31, 0xC1] (fun s => s.RIP = 0x10633d) (xorR32R32Effect 0x10633d 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10633d 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10633d 0xc1 (by decide)) pre_rip
  have f805 : InstrSpec 0x10633f [0x66, 0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x10633f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10633f + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x10633f 8 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10633f 8 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m16_r16_effect_step 0x10633f 1 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f806 : InstrSpec 0x106347 [0x0F, 0xB7, 0x84, 0x24, 0xB2, 0x00, 0x00, 0x00] (LoadPre 0x106347 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb2)) s (0x106347 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106347 8 0 (.sib 4 none 0 (.d32 0xb2)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106347 8 0 (.sib 4 none 0 (.d32 0xb2))).toInstrSpec (movzx_r32_m16_effect_step 0x106347 0 (.sib 4 none 0 (.d32 0xb2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f807 : InstrSpec 0x10634f [0x89, 0xC1] (fun s => s.RIP = 0x10634f) (movR32R32Effect 0x10634f 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10634f 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x10634f 0xc1 (by decide)) pre_rip
  have f808 : InstrSpec 0x106351 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x106351) (shrR32Effect 0x106351 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x106351 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x106351 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f809 : InstrSpec 0x106354 [0x31, 0xC1] (fun s => s.RIP = 0x106354) (xorR32R32Effect 0x106354 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106354 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106354 0xc1 (by decide)) pre_rip
  have f810 : InstrSpec 0x106356 [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x106356) (andR32Imm32Effect 0x106356 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106356 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x106356 0xe1 0x3030 (by decide) (by decide)) pre_rip
  have f811 : InstrSpec 0x10635c [0x31, 0xC8] (fun s => s.RIP = 0x10635c) (xorR32R32Effect 0x10635c 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10635c 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10635c 0xc8 (by decide)) pre_rip
  have f812 : InstrSpec 0x10635e [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x10635e) (shlR32Effect 0x10635e 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10635e 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x10635e 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f813 : InstrSpec 0x106361 [0x31, 0xC1] (fun s => s.RIP = 0x106361) (xorR32R32Effect 0x106361 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106361 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106361 0xc1 (by decide)) pre_rip
  have f814 : InstrSpec 0x106363 [0x66, 0x89, 0x8C, 0x24, 0xB2, 0x00, 0x00, 0x00] (StorePre 0x106363 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb2)) s (0x106363 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106363 8 1 (.sib 4 none 0 (.d32 0xb2)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106363 8 1 (.sib 4 none 0 (.d32 0xb2))).toInstrSpec (mov_m16_r16_effect_step 0x106363 1 (.sib 4 none 0 (.d32 0xb2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f815 : InstrSpec 0x10636b [0x0F, 0xB7, 0x84, 0x24, 0xB4, 0x00, 0x00, 0x00] (LoadPre 0x10636b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x10636b + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x10636b 8 0 (.sib 4 none 0 (.d32 0xb4)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10636b 8 0 (.sib 4 none 0 (.d32 0xb4))).toInstrSpec (movzx_r32_m16_effect_step 0x10636b 0 (.sib 4 none 0 (.d32 0xb4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f816 : InstrSpec 0x106373 [0x89, 0xC1] (fun s => s.RIP = 0x106373) (movR32R32Effect 0x106373 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106373 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x106373 0xc1 (by decide)) pre_rip
  have f817 : InstrSpec 0x106375 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x106375) (shrR32Effect 0x106375 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x106375 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x106375 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f818 : InstrSpec 0x106378 [0x31, 0xC1] (fun s => s.RIP = 0x106378) (xorR32R32Effect 0x106378 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106378 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106378 0xc1 (by decide)) pre_rip
  have f819 : InstrSpec 0x10637a [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x10637a) (andR32Imm32Effect 0x10637a 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10637a 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x10637a 0xe1 0x3030 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1600) (RestInside.out (n := 1600) f800 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1601) (ρ' := [(0, 1594), (1, 1600), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106332) f800 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1602) (RestInside.out (n := 1602) f801 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1603) (ρ' := [(0, 1594), (1, 1602), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106338) f801 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1604) (RestInside.out (n := 1604) f802 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1605) (ρ' := [(0, 1604), (1, 1602), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10633a) f802 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1606) (RestInside.out (n := 1606) f803 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1607) (ρ' := [(0, 1604), (1, 1606), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10633d) f803 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1608) (RestInside.out (n := 1608) f804 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1609) (ρ' := [(0, 1604), (1, 1608), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10633f) f804 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1610) (RestInside.exec (n := 1610) (ρ' := [(0, 1604), (1, 1608), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106347) f805 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1611) (RestInside.out (n := 1611) f806 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1612) (ρ' := [(0, 1611), (1, 1608), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10634f) f806 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1613) (RestInside.out (n := 1613) f807 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1614) (ρ' := [(0, 1611), (1, 1613), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106351) f807 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1615) (RestInside.out (n := 1615) f808 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1616) (ρ' := [(0, 1611), (1, 1615), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106354) f808 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1617) (RestInside.out (n := 1617) f809 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1618) (ρ' := [(0, 1611), (1, 1617), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106356) f809 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1619) (RestInside.out (n := 1619) f810 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1620) (ρ' := [(0, 1611), (1, 1619), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10635c) f810 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1621) (RestInside.out (n := 1621) f811 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1622) (ρ' := [(0, 1621), (1, 1619), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10635e) f811 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1623) (RestInside.out (n := 1623) f812 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1624) (ρ' := [(0, 1621), (1, 1623), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106361) f812 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1625) (RestInside.out (n := 1625) f813 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1626) (ρ' := [(0, 1621), (1, 1625), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106363) f813 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1627) (RestInside.exec (n := 1627) (ρ' := [(0, 1621), (1, 1625), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10636b) f814 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1628) (RestInside.out (n := 1628) f815 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1629) (ρ' := [(0, 1628), (1, 1625), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106373) f815 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1630) (RestInside.out (n := 1630) f816 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1631) (ρ' := [(0, 1628), (1, 1630), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106375) f816 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1632) (RestInside.out (n := 1632) f817 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1633) (ρ' := [(0, 1628), (1, 1632), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106378) f817 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1634) (RestInside.out (n := 1634) f818 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1635) (ρ' := [(0, 1628), (1, 1634), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10637a) f818 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1636) (RestInside.out (n := 1636) f819 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1637) (ρ' := [(0, 1628), (1, 1636), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106380) f819 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_41 code

theorem rest_l10593a_39 [Bindings] (code : CodeMap) :
    Rest (n := 1561) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1559), (1, 1555), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      412 0x1062dc bytes_l10593a_39 b_l10593a_39 := by
  have f780 : InstrSpec 0x1062dc [0x66, 0x89, 0x84, 0x24, 0xAA, 0x00, 0x00, 0x00] (StorePre 0x1062dc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaa)) s (0x1062dc + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1062dc 8 0 (.sib 4 none 0 (.d32 0xaa)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1062dc 8 0 (.sib 4 none 0 (.d32 0xaa))).toInstrSpec (mov_m16_r16_effect_step 0x1062dc 0 (.sib 4 none 0 (.d32 0xaa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f781 : InstrSpec 0x1062e4 [0x0F, 0xB7, 0x84, 0x24, 0xAC, 0x00, 0x00, 0x00] (LoadPre 0x1062e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xac)) s (0x1062e4 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1062e4 8 0 (.sib 4 none 0 (.d32 0xac)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1062e4 8 0 (.sib 4 none 0 (.d32 0xac))).toInstrSpec (movzx_r32_m16_effect_step 0x1062e4 0 (.sib 4 none 0 (.d32 0xac)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f782 : InstrSpec 0x1062ec [0x41, 0x89, 0xC5] (fun s => s.RIP = 0x1062ec) (movR32R32Effect 0x1062ec 3 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x1062ec 3 13 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x1062ec 0x41 0xc5 (by decide) (by decide)) pre_rip
  have f783 : InstrSpec 0x1062ef [0x41, 0xC1, 0xED, 0x02] (fun s => s.RIP = 0x1062ef) (shrR32Effect 0x1062ef 4 13 2)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR32Effect_footprint 0x1062ef 4 13 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x1062ef 0x41 0xed 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f784 : InstrSpec 0x1062f3 [0x41, 0x31, 0xC5] (fun s => s.RIP = 0x1062f3) (xorR32R32Effect 0x1062f3 3 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1062f3 3 13 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x1062f3 0x41 0xc5 (by decide) (by decide)) pre_rip
  have f785 : InstrSpec 0x1062f6 [0x41, 0x81, 0xE5, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x1062f6) (andR32Imm32Effect 0x1062f6 7 13 0x3030)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1062f6 7 13 0x3030).toInstrSpec (and_r32_imm32_rex_effect_step 0x1062f6 0x41 0xe5 0x3030 (by decide) (by decide) (by decide)) pre_rip
  have f786 : InstrSpec 0x1062fd [0x44, 0x31, 0xE8] (fun s => s.RIP = 0x1062fd) (xorR32R32Effect 0x1062fd 3 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1062fd 3 0 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x1062fd 0x44 0xe8 (by decide) (by decide)) pre_rip
  have f787 : InstrSpec 0x106300 [0x41, 0xC1, 0xE5, 0x02] (fun s => s.RIP = 0x106300) (shlR32Effect 0x106300 4 13 2)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shlR32Effect_footprint 0x106300 4 13 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x106300 0x41 0xe5 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f788 : InstrSpec 0x106304 [0x41, 0x31, 0xC5] (fun s => s.RIP = 0x106304) (xorR32R32Effect 0x106304 3 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106304 3 13 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x106304 0x41 0xc5 (by decide) (by decide)) pre_rip
  have f789 : InstrSpec 0x106307 [0x0F, 0xB7, 0x84, 0x24, 0xAE, 0x00, 0x00, 0x00] (LoadPre 0x106307 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xae)) s (0x106307 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106307 8 0 (.sib 4 none 0 (.d32 0xae)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106307 8 0 (.sib 4 none 0 (.d32 0xae))).toInstrSpec (movzx_r32_m16_effect_step 0x106307 0 (.sib 4 none 0 (.d32 0xae)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f790 : InstrSpec 0x10630f [0x89, 0xC5] (fun s => s.RIP = 0x10630f) (movR32R32Effect 0x10630f 2 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x10630f 2 5 0).toInstrSpec (mov_r32_r32_effect_step 0x10630f 0xc5 (by decide)) pre_rip
  have f791 : InstrSpec 0x106311 [0xC1, 0xED, 0x02] (fun s => s.RIP = 0x106311) (shrR32Effect 0x106311 3 5 2)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR32Effect_footprint 0x106311 3 5 2).toInstrSpec (shr_r32_imm8_effect_step 0x106311 0xed 0x2 (by decide) (by decide)) pre_rip
  have f792 : InstrSpec 0x106314 [0x31, 0xC5] (fun s => s.RIP = 0x106314) (xorR32R32Effect 0x106314 2 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106314 2 5 0).toInstrSpec (xor_r32_r32_effect_step 0x106314 0xc5 (by decide)) pre_rip
  have f793 : InstrSpec 0x106316 [0x81, 0xE5, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x106316) (andR32Imm32Effect 0x106316 6 5 0x3030)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106316 6 5 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x106316 0xe5 0x3030 (by decide) (by decide)) pre_rip
  have f794 : InstrSpec 0x10631c [0x31, 0xE8] (fun s => s.RIP = 0x10631c) (xorR32R32Effect 0x10631c 2 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10631c 2 0 5).toInstrSpec (xor_r32_r32_effect_step 0x10631c 0xe8 (by decide)) pre_rip
  have f795 : InstrSpec 0x10631e [0xC1, 0xE5, 0x02] (fun s => s.RIP = 0x10631e) (shlR32Effect 0x10631e 3 5 2)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shlR32Effect_footprint 0x10631e 3 5 2).toInstrSpec (shl_r32_imm8_effect_step 0x10631e 0xe5 0x2 (by decide) (by decide)) pre_rip
  have f796 : InstrSpec 0x106321 [0x31, 0xC5] (fun s => s.RIP = 0x106321) (xorR32R32Effect 0x106321 2 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106321 2 5 0).toInstrSpec (xor_r32_r32_effect_step 0x106321 0xc5 (by decide)) pre_rip
  have f797 : InstrSpec 0x106323 [0x0F, 0xB7, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x106323 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x106323 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106323 8 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106323 8 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (movzx_r32_m16_effect_step 0x106323 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f798 : InstrSpec 0x10632b [0x89, 0xC1] (fun s => s.RIP = 0x10632b) (movR32R32Effect 0x10632b 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10632b 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x10632b 0xc1 (by decide)) pre_rip
  have f799 : InstrSpec 0x10632d [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x10632d) (shrR32Effect 0x10632d 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10632d 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x10632d 0xe9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1561) (RestInside.exec (n := 1561) (ρ' := [(0, 1559), (1, 1555), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062e4) f780 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1562) (RestInside.out (n := 1562) f781 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1563) (ρ' := [(0, 1562), (1, 1555), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062ec) f781 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1564) (RestInside.out (n := 1564) f782 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1565) (ρ' := [(0, 1562), (1, 1555), (4, 4), (9, 1033), (12, 1343), (13, 1564), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062ef) f782 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1566) (RestInside.out (n := 1566) f783 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1567) (ρ' := [(0, 1562), (1, 1555), (4, 4), (9, 1033), (12, 1343), (13, 1566), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062f3) f783 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1568) (RestInside.out (n := 1568) f784 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1569) (ρ' := [(0, 1562), (1, 1555), (4, 4), (9, 1033), (12, 1343), (13, 1568), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062f6) f784 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1570) (RestInside.out (n := 1570) f785 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1571) (ρ' := [(0, 1562), (1, 1555), (4, 4), (9, 1033), (12, 1343), (13, 1570), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062fd) f785 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1572) (RestInside.out (n := 1572) f786 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1573) (ρ' := [(0, 1572), (1, 1555), (4, 4), (9, 1033), (12, 1343), (13, 1570), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106300) f786 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1574) (RestInside.out (n := 1574) f787 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1575) (ρ' := [(0, 1572), (1, 1555), (4, 4), (9, 1033), (12, 1343), (13, 1574), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106304) f787 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1576) (RestInside.out (n := 1576) f788 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1577) (ρ' := [(0, 1572), (1, 1555), (4, 4), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106307) f788 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1578) (RestInside.out (n := 1578) f789 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1579) (ρ' := [(0, 1578), (1, 1555), (4, 4), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10630f) f789 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1580) (RestInside.out (n := 1580) f790 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1581) (ρ' := [(0, 1578), (1, 1555), (4, 4), (5, 1580), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106311) f790 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1582) (RestInside.out (n := 1582) f791 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1583) (ρ' := [(0, 1578), (1, 1555), (4, 4), (5, 1582), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106314) f791 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1584) (RestInside.out (n := 1584) f792 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1585) (ρ' := [(0, 1578), (1, 1555), (4, 4), (5, 1584), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106316) f792 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1586) (RestInside.out (n := 1586) f793 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1587) (ρ' := [(0, 1578), (1, 1555), (4, 4), (5, 1586), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10631c) f793 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1588) (RestInside.out (n := 1588) f794 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1589) (ρ' := [(0, 1588), (1, 1555), (4, 4), (5, 1586), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10631e) f794 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1590) (RestInside.out (n := 1590) f795 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1591) (ρ' := [(0, 1588), (1, 1555), (4, 4), (5, 1590), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106321) f795 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1592) (RestInside.out (n := 1592) f796 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1593) (ρ' := [(0, 1588), (1, 1555), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106323) f796 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1594) (RestInside.out (n := 1594) f797 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1595) (ρ' := [(0, 1594), (1, 1555), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10632b) f797 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1596) (RestInside.out (n := 1596) f798 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1597) (ρ' := [(0, 1594), (1, 1596), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10632d) f798 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1598) (RestInside.out (n := 1598) f799 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1599) (ρ' := [(0, 1594), (1, 1598), (4, 4), (5, 1592), (9, 1033), (12, 1343), (13, 1576), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106330) f799 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_40 code

theorem rest_l10593a_38 [Bindings] (code : CodeMap) :
    Rest (n := 1522) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1520), (1, 1514), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      432 0x10629c bytes_l10593a_38 b_l10593a_38 := by
  have f760 : InstrSpec 0x10629c [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x10629c) (andEaxImm32Effect 0x10629c 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x10629c 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x10629c 0x5050) pre_rip
  have f761 : InstrSpec 0x1062a1 [0x31, 0xC1] (fun s => s.RIP = 0x1062a1) (xorR32R32Effect 0x1062a1 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1062a1 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1062a1 0xc1 (by decide)) pre_rip
  have f762 : InstrSpec 0x1062a3 [0x01, 0xC0] (fun s => s.RIP = 0x1062a3) (addR32R32Effect 0x1062a3 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1062a3 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x1062a3 0xc0 (by decide)) pre_rip
  have f763 : InstrSpec 0x1062a5 [0x31, 0xC8] (fun s => s.RIP = 0x1062a5) (xorR32R32Effect 0x1062a5 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1062a5 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1062a5 0xc8 (by decide)) pre_rip
  have f764 : InstrSpec 0x1062a7 [0x66, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x1062a7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1062a7 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1062a7 8 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1062a7 8 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m16_r16_effect_step 0x1062a7 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f765 : InstrSpec 0x1062af [0x0F, 0xB7, 0x84, 0x24, 0xAA, 0x00, 0x00, 0x00] (LoadPre 0x1062af (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaa)) s (0x1062af + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1062af 8 0 (.sib 4 none 0 (.d32 0xaa)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1062af 8 0 (.sib 4 none 0 (.d32 0xaa))).toInstrSpec (movzx_r32_m16_effect_step 0x1062af 0 (.sib 4 none 0 (.d32 0xaa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f766 : InstrSpec 0x1062b7 [0x89, 0xC1] (fun s => s.RIP = 0x1062b7) (movR32R32Effect 0x1062b7 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1062b7 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1062b7 0xc1 (by decide)) pre_rip
  have f767 : InstrSpec 0x1062b9 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x1062b9) (shrR32Effect 0x1062b9 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1062b9 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x1062b9 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f768 : InstrSpec 0x1062bc [0x31, 0xC1] (fun s => s.RIP = 0x1062bc) (xorR32R32Effect 0x1062bc 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1062bc 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1062bc 0xc1 (by decide)) pre_rip
  have f769 : InstrSpec 0x1062be [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x1062be) (andR32Imm32Effect 0x1062be 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1062be 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x1062be 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f770 : InstrSpec 0x1062c4 [0x31, 0xC8] (fun s => s.RIP = 0x1062c4) (xorR32R32Effect 0x1062c4 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1062c4 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1062c4 0xc8 (by decide)) pre_rip
  have f771 : InstrSpec 0x1062c6 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x1062c6) (shlR32Effect 0x1062c6 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x1062c6 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x1062c6 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f772 : InstrSpec 0x1062c9 [0x31, 0xC1] (fun s => s.RIP = 0x1062c9) (xorR32R32Effect 0x1062c9 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1062c9 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1062c9 0xc1 (by decide)) pre_rip
  have f773 : InstrSpec 0x1062cb [0x89, 0xC8] (fun s => s.RIP = 0x1062cb) (movR32R32Effect 0x1062cb 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1062cb 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x1062cb 0xc8 (by decide)) pre_rip
  have f774 : InstrSpec 0x1062cd [0xD1, 0xE8] (fun s => s.RIP = 0x1062cd) (shrR32Effect 0x1062cd 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x1062cd 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x1062cd 0xe8 (by decide) (by decide)) pre_rip
  have f775 : InstrSpec 0x1062cf [0x31, 0xC8] (fun s => s.RIP = 0x1062cf) (xorR32R32Effect 0x1062cf 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1062cf 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1062cf 0xc8 (by decide)) pre_rip
  have f776 : InstrSpec 0x1062d1 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1062d1) (andEaxImm32Effect 0x1062d1 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x1062d1 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x1062d1 0x5050) pre_rip
  have f777 : InstrSpec 0x1062d6 [0x31, 0xC1] (fun s => s.RIP = 0x1062d6) (xorR32R32Effect 0x1062d6 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1062d6 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1062d6 0xc1 (by decide)) pre_rip
  have f778 : InstrSpec 0x1062d8 [0x01, 0xC0] (fun s => s.RIP = 0x1062d8) (addR32R32Effect 0x1062d8 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1062d8 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x1062d8 0xc0 (by decide)) pre_rip
  have f779 : InstrSpec 0x1062da [0x31, 0xC8] (fun s => s.RIP = 0x1062da) (xorR32R32Effect 0x1062da 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1062da 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1062da 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 1522) (RestInside.out (n := 1522) f760 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1523) (ρ' := [(0, 1522), (1, 1514), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062a1) f760 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1524) (RestInside.out (n := 1524) f761 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1525) (ρ' := [(0, 1522), (1, 1524), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062a3) f761 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1526) (RestInside.out (n := 1526) f762 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1527) (ρ' := [(0, 1526), (1, 1524), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062a5) f762 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1528) (RestInside.out (n := 1528) f763 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1529) (ρ' := [(0, 1528), (1, 1524), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062a7) f763 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1530) (RestInside.exec (n := 1530) (ρ' := [(0, 1528), (1, 1524), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062af) f764 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1531) (RestInside.out (n := 1531) f765 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1532) (ρ' := [(0, 1531), (1, 1524), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062b7) f765 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1533) (RestInside.out (n := 1533) f766 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1534) (ρ' := [(0, 1531), (1, 1533), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062b9) f766 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1535) (RestInside.out (n := 1535) f767 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1536) (ρ' := [(0, 1531), (1, 1535), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062bc) f767 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1537) (RestInside.out (n := 1537) f768 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1538) (ρ' := [(0, 1531), (1, 1537), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062be) f768 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1539) (RestInside.out (n := 1539) f769 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1540) (ρ' := [(0, 1531), (1, 1539), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062c4) f769 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1541) (RestInside.out (n := 1541) f770 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1542) (ρ' := [(0, 1541), (1, 1539), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062c6) f770 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1543) (RestInside.out (n := 1543) f771 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1544) (ρ' := [(0, 1541), (1, 1543), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062c9) f771 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1545) (RestInside.out (n := 1545) f772 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1546) (ρ' := [(0, 1541), (1, 1545), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062cb) f772 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1547) (RestInside.out (n := 1547) f773 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1548) (ρ' := [(0, 1547), (1, 1545), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062cd) f773 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1549) (RestInside.out (n := 1549) f774 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1550) (ρ' := [(0, 1549), (1, 1545), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062cf) f774 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1551) (RestInside.out (n := 1551) f775 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1552) (ρ' := [(0, 1551), (1, 1545), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062d1) f775 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1553) (RestInside.out (n := 1553) f776 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1554) (ρ' := [(0, 1553), (1, 1545), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062d6) f776 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1555) (RestInside.out (n := 1555) f777 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1556) (ρ' := [(0, 1553), (1, 1555), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062d8) f777 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1557) (RestInside.out (n := 1557) f778 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1558) (ρ' := [(0, 1557), (1, 1555), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062da) f778 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1559) (RestInside.out (n := 1559) f779 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1560) (ρ' := [(0, 1559), (1, 1555), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062dc) f779 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_39 code

theorem rest_l10593a_37 [Bindings] (code : CodeMap) :
    Rest (n := 1483) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1479), (1, 1481), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      452 0x10625f bytes_l10593a_37 b_l10593a_37 := by
  have f740 : InstrSpec 0x10625f [0x31, 0xC1] (fun s => s.RIP = 0x10625f) (xorR32R32Effect 0x10625f 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10625f 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10625f 0xc1 (by decide)) pre_rip
  have f741 : InstrSpec 0x106261 [0x89, 0xC8] (fun s => s.RIP = 0x106261) (movR32R32Effect 0x106261 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106261 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x106261 0xc8 (by decide)) pre_rip
  have f742 : InstrSpec 0x106263 [0xD1, 0xE8] (fun s => s.RIP = 0x106263) (shrR32Effect 0x106263 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x106263 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x106263 0xe8 (by decide) (by decide)) pre_rip
  have f743 : InstrSpec 0x106265 [0x31, 0xC8] (fun s => s.RIP = 0x106265) (xorR32R32Effect 0x106265 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106265 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106265 0xc8 (by decide)) pre_rip
  have f744 : InstrSpec 0x106267 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x106267) (andEaxImm32Effect 0x106267 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106267 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x106267 0x5050) pre_rip
  have f745 : InstrSpec 0x10626c [0x31, 0xC1] (fun s => s.RIP = 0x10626c) (xorR32R32Effect 0x10626c 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10626c 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10626c 0xc1 (by decide)) pre_rip
  have f746 : InstrSpec 0x10626e [0x01, 0xC0] (fun s => s.RIP = 0x10626e) (addR32R32Effect 0x10626e 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10626e 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x10626e 0xc0 (by decide)) pre_rip
  have f747 : InstrSpec 0x106270 [0x31, 0xC8] (fun s => s.RIP = 0x106270) (xorR32R32Effect 0x106270 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106270 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106270 0xc8 (by decide)) pre_rip
  have f748 : InstrSpec 0x106272 [0x66, 0x89, 0x84, 0x24, 0xA6, 0x00, 0x00, 0x00] (StorePre 0x106272 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa6)) s (0x106272 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106272 8 0 (.sib 4 none 0 (.d32 0xa6)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106272 8 0 (.sib 4 none 0 (.d32 0xa6))).toInstrSpec (mov_m16_r16_effect_step 0x106272 0 (.sib 4 none 0 (.d32 0xa6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f749 : InstrSpec 0x10627a [0x0F, 0xB7, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x10627a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10627a + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x10627a 8 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10627a 8 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (movzx_r32_m16_effect_step 0x10627a 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f750 : InstrSpec 0x106282 [0x89, 0xC1] (fun s => s.RIP = 0x106282) (movR32R32Effect 0x106282 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106282 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x106282 0xc1 (by decide)) pre_rip
  have f751 : InstrSpec 0x106284 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x106284) (shrR32Effect 0x106284 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x106284 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x106284 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f752 : InstrSpec 0x106287 [0x31, 0xC1] (fun s => s.RIP = 0x106287) (xorR32R32Effect 0x106287 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106287 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106287 0xc1 (by decide)) pre_rip
  have f753 : InstrSpec 0x106289 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x106289) (andR32Imm32Effect 0x106289 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106289 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x106289 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f754 : InstrSpec 0x10628f [0x31, 0xC8] (fun s => s.RIP = 0x10628f) (xorR32R32Effect 0x10628f 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10628f 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10628f 0xc8 (by decide)) pre_rip
  have f755 : InstrSpec 0x106291 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x106291) (shlR32Effect 0x106291 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x106291 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x106291 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f756 : InstrSpec 0x106294 [0x31, 0xC1] (fun s => s.RIP = 0x106294) (xorR32R32Effect 0x106294 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106294 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106294 0xc1 (by decide)) pre_rip
  have f757 : InstrSpec 0x106296 [0x89, 0xC8] (fun s => s.RIP = 0x106296) (movR32R32Effect 0x106296 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106296 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x106296 0xc8 (by decide)) pre_rip
  have f758 : InstrSpec 0x106298 [0xD1, 0xE8] (fun s => s.RIP = 0x106298) (shrR32Effect 0x106298 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x106298 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x106298 0xe8 (by decide) (by decide)) pre_rip
  have f759 : InstrSpec 0x10629a [0x31, 0xC8] (fun s => s.RIP = 0x10629a) (xorR32R32Effect 0x10629a 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10629a 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10629a 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 1483) (RestInside.out (n := 1483) f740 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1484) (ρ' := [(0, 1479), (1, 1483), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106261) f740 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1485) (RestInside.out (n := 1485) f741 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1486) (ρ' := [(0, 1485), (1, 1483), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106263) f741 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1487) (RestInside.out (n := 1487) f742 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1488) (ρ' := [(0, 1487), (1, 1483), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106265) f742 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1489) (RestInside.out (n := 1489) f743 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1490) (ρ' := [(0, 1489), (1, 1483), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106267) f743 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1491) (RestInside.out (n := 1491) f744 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1492) (ρ' := [(0, 1491), (1, 1483), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10626c) f744 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1493) (RestInside.out (n := 1493) f745 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1494) (ρ' := [(0, 1491), (1, 1493), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10626e) f745 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1495) (RestInside.out (n := 1495) f746 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1496) (ρ' := [(0, 1495), (1, 1493), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106270) f746 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1497) (RestInside.out (n := 1497) f747 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1498) (ρ' := [(0, 1497), (1, 1493), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106272) f747 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1499) (RestInside.exec (n := 1499) (ρ' := [(0, 1497), (1, 1493), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10627a) f748 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1500) (RestInside.out (n := 1500) f749 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1501) (ρ' := [(0, 1500), (1, 1493), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106282) f749 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1502) (RestInside.out (n := 1502) f750 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1503) (ρ' := [(0, 1500), (1, 1502), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106284) f750 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1504) (RestInside.out (n := 1504) f751 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1505) (ρ' := [(0, 1500), (1, 1504), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106287) f751 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1506) (RestInside.out (n := 1506) f752 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1507) (ρ' := [(0, 1500), (1, 1506), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106289) f752 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1508) (RestInside.out (n := 1508) f753 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1509) (ρ' := [(0, 1500), (1, 1508), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10628f) f753 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1510) (RestInside.out (n := 1510) f754 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1511) (ρ' := [(0, 1510), (1, 1508), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106291) f754 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1512) (RestInside.out (n := 1512) f755 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1513) (ρ' := [(0, 1510), (1, 1512), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106294) f755 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1514) (RestInside.out (n := 1514) f756 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1515) (ρ' := [(0, 1510), (1, 1514), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106296) f756 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1516) (RestInside.out (n := 1516) f757 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1517) (ρ' := [(0, 1516), (1, 1514), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106298) f757 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1518) (RestInside.out (n := 1518) f758 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1519) (ρ' := [(0, 1518), (1, 1514), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10629a) f758 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1520) (RestInside.out (n := 1520) f759 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1521) (ρ' := [(0, 1520), (1, 1514), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10629c) f759 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_38 code

theorem rest_l10593a_36 [Bindings] (code : CodeMap) :
    Rest (n := 1444) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1438), (1, 1442), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      472 0x10621d bytes_l10593a_36 b_l10593a_36 := by
  have f720 : InstrSpec 0x10621d [0x31, 0xC1] (fun s => s.RIP = 0x10621d) (xorR32R32Effect 0x10621d 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10621d 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10621d 0xc1 (by decide)) pre_rip
  have f721 : InstrSpec 0x10621f [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x10621f) (andR32Imm32Effect 0x10621f 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10621f 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x10621f 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f722 : InstrSpec 0x106225 [0x31, 0xC8] (fun s => s.RIP = 0x106225) (xorR32R32Effect 0x106225 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106225 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106225 0xc8 (by decide)) pre_rip
  have f723 : InstrSpec 0x106227 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x106227) (shlR32Effect 0x106227 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x106227 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x106227 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f724 : InstrSpec 0x10622a [0x31, 0xC1] (fun s => s.RIP = 0x10622a) (xorR32R32Effect 0x10622a 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10622a 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10622a 0xc1 (by decide)) pre_rip
  have f725 : InstrSpec 0x10622c [0x89, 0xC8] (fun s => s.RIP = 0x10622c) (movR32R32Effect 0x10622c 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x10622c 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x10622c 0xc8 (by decide)) pre_rip
  have f726 : InstrSpec 0x10622e [0xD1, 0xE8] (fun s => s.RIP = 0x10622e) (shrR32Effect 0x10622e 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x10622e 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x10622e 0xe8 (by decide) (by decide)) pre_rip
  have f727 : InstrSpec 0x106230 [0x31, 0xC8] (fun s => s.RIP = 0x106230) (xorR32R32Effect 0x106230 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106230 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106230 0xc8 (by decide)) pre_rip
  have f728 : InstrSpec 0x106232 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x106232) (andEaxImm32Effect 0x106232 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106232 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x106232 0x5050) pre_rip
  have f729 : InstrSpec 0x106237 [0x31, 0xC1] (fun s => s.RIP = 0x106237) (xorR32R32Effect 0x106237 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106237 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106237 0xc1 (by decide)) pre_rip
  have f730 : InstrSpec 0x106239 [0x01, 0xC0] (fun s => s.RIP = 0x106239) (addR32R32Effect 0x106239 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x106239 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x106239 0xc0 (by decide)) pre_rip
  have f731 : InstrSpec 0x10623b [0x31, 0xC8] (fun s => s.RIP = 0x10623b) (xorR32R32Effect 0x10623b 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10623b 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10623b 0xc8 (by decide)) pre_rip
  have f732 : InstrSpec 0x10623d [0x66, 0x89, 0x84, 0x24, 0xA4, 0x00, 0x00, 0x00] (StorePre 0x10623d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x10623d + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x10623d 8 0 (.sib 4 none 0 (.d32 0xa4)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10623d 8 0 (.sib 4 none 0 (.d32 0xa4))).toInstrSpec (mov_m16_r16_effect_step 0x10623d 0 (.sib 4 none 0 (.d32 0xa4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f733 : InstrSpec 0x106245 [0x0F, 0xB7, 0x84, 0x24, 0xA6, 0x00, 0x00, 0x00] (LoadPre 0x106245 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa6)) s (0x106245 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106245 8 0 (.sib 4 none 0 (.d32 0xa6)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106245 8 0 (.sib 4 none 0 (.d32 0xa6))).toInstrSpec (movzx_r32_m16_effect_step 0x106245 0 (.sib 4 none 0 (.d32 0xa6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f734 : InstrSpec 0x10624d [0x89, 0xC1] (fun s => s.RIP = 0x10624d) (movR32R32Effect 0x10624d 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10624d 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x10624d 0xc1 (by decide)) pre_rip
  have f735 : InstrSpec 0x10624f [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x10624f) (shrR32Effect 0x10624f 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10624f 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x10624f 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f736 : InstrSpec 0x106252 [0x31, 0xC1] (fun s => s.RIP = 0x106252) (xorR32R32Effect 0x106252 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106252 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106252 0xc1 (by decide)) pre_rip
  have f737 : InstrSpec 0x106254 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x106254) (andR32Imm32Effect 0x106254 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106254 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x106254 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f738 : InstrSpec 0x10625a [0x31, 0xC8] (fun s => s.RIP = 0x10625a) (xorR32R32Effect 0x10625a 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10625a 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10625a 0xc8 (by decide)) pre_rip
  have f739 : InstrSpec 0x10625c [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x10625c) (shlR32Effect 0x10625c 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10625c 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x10625c 0xe1 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1444) (RestInside.out (n := 1444) f720 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1445) (ρ' := [(0, 1438), (1, 1444), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10621f) f720 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1446) (RestInside.out (n := 1446) f721 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1447) (ρ' := [(0, 1438), (1, 1446), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106225) f721 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1448) (RestInside.out (n := 1448) f722 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1449) (ρ' := [(0, 1448), (1, 1446), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106227) f722 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1450) (RestInside.out (n := 1450) f723 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1451) (ρ' := [(0, 1448), (1, 1450), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10622a) f723 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1452) (RestInside.out (n := 1452) f724 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1453) (ρ' := [(0, 1448), (1, 1452), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10622c) f724 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1454) (RestInside.out (n := 1454) f725 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1455) (ρ' := [(0, 1454), (1, 1452), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10622e) f725 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1456) (RestInside.out (n := 1456) f726 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1457) (ρ' := [(0, 1456), (1, 1452), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106230) f726 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1458) (RestInside.out (n := 1458) f727 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1459) (ρ' := [(0, 1458), (1, 1452), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106232) f727 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1460) (RestInside.out (n := 1460) f728 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1461) (ρ' := [(0, 1460), (1, 1452), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106237) f728 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1462) (RestInside.out (n := 1462) f729 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1463) (ρ' := [(0, 1460), (1, 1462), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106239) f729 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1464) (RestInside.out (n := 1464) f730 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1465) (ρ' := [(0, 1464), (1, 1462), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10623b) f730 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1466) (RestInside.out (n := 1466) f731 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1467) (ρ' := [(0, 1466), (1, 1462), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10623d) f731 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1468) (RestInside.exec (n := 1468) (ρ' := [(0, 1466), (1, 1462), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106245) f732 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1469) (RestInside.out (n := 1469) f733 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1470) (ρ' := [(0, 1469), (1, 1462), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10624d) f733 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1471) (RestInside.out (n := 1471) f734 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1472) (ρ' := [(0, 1469), (1, 1471), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10624f) f734 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1473) (RestInside.out (n := 1473) f735 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1474) (ρ' := [(0, 1469), (1, 1473), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106252) f735 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1475) (RestInside.out (n := 1475) f736 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1476) (ρ' := [(0, 1469), (1, 1475), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106254) f736 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1477) (RestInside.out (n := 1477) f737 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1478) (ρ' := [(0, 1469), (1, 1477), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10625a) f737 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1479) (RestInside.out (n := 1479) f738 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1480) (ρ' := [(0, 1479), (1, 1477), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10625c) f738 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1481) (RestInside.out (n := 1481) f739 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1482) (ρ' := [(0, 1479), (1, 1481), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10625f) f739 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_37 code

theorem rest_l10593a_35 [Bindings] (code : CodeMap) :
    Rest (n := 1406) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1404), (1, 1400), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      492 0x1061d3 bytes_l10593a_35 b_l10593a_35 := by
  have f700 : InstrSpec 0x1061d3 [0x66, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x1061d3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1061d3 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1061d3 8 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1061d3 8 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m16_r16_effect_step 0x1061d3 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f701 : InstrSpec 0x1061db [0x0F, 0xB7, 0x84, 0x24, 0xA2, 0x00, 0x00, 0x00] (LoadPre 0x1061db (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa2)) s (0x1061db + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1061db 8 0 (.sib 4 none 0 (.d32 0xa2)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1061db 8 0 (.sib 4 none 0 (.d32 0xa2))).toInstrSpec (movzx_r32_m16_effect_step 0x1061db 0 (.sib 4 none 0 (.d32 0xa2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f702 : InstrSpec 0x1061e3 [0x89, 0xC1] (fun s => s.RIP = 0x1061e3) (movR32R32Effect 0x1061e3 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1061e3 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1061e3 0xc1 (by decide)) pre_rip
  have f703 : InstrSpec 0x1061e5 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x1061e5) (shrR32Effect 0x1061e5 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1061e5 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x1061e5 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f704 : InstrSpec 0x1061e8 [0x31, 0xC1] (fun s => s.RIP = 0x1061e8) (xorR32R32Effect 0x1061e8 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1061e8 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1061e8 0xc1 (by decide)) pre_rip
  have f705 : InstrSpec 0x1061ea [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x1061ea) (andR32Imm32Effect 0x1061ea 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1061ea 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x1061ea 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f706 : InstrSpec 0x1061f0 [0x31, 0xC8] (fun s => s.RIP = 0x1061f0) (xorR32R32Effect 0x1061f0 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1061f0 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1061f0 0xc8 (by decide)) pre_rip
  have f707 : InstrSpec 0x1061f2 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x1061f2) (shlR32Effect 0x1061f2 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x1061f2 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x1061f2 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f708 : InstrSpec 0x1061f5 [0x31, 0xC1] (fun s => s.RIP = 0x1061f5) (xorR32R32Effect 0x1061f5 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1061f5 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1061f5 0xc1 (by decide)) pre_rip
  have f709 : InstrSpec 0x1061f7 [0x89, 0xC8] (fun s => s.RIP = 0x1061f7) (movR32R32Effect 0x1061f7 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1061f7 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x1061f7 0xc8 (by decide)) pre_rip
  have f710 : InstrSpec 0x1061f9 [0xD1, 0xE8] (fun s => s.RIP = 0x1061f9) (shrR32Effect 0x1061f9 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x1061f9 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x1061f9 0xe8 (by decide) (by decide)) pre_rip
  have f711 : InstrSpec 0x1061fb [0x31, 0xC8] (fun s => s.RIP = 0x1061fb) (xorR32R32Effect 0x1061fb 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1061fb 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1061fb 0xc8 (by decide)) pre_rip
  have f712 : InstrSpec 0x1061fd [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1061fd) (andEaxImm32Effect 0x1061fd 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x1061fd 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x1061fd 0x5050) pre_rip
  have f713 : InstrSpec 0x106202 [0x31, 0xC1] (fun s => s.RIP = 0x106202) (xorR32R32Effect 0x106202 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106202 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106202 0xc1 (by decide)) pre_rip
  have f714 : InstrSpec 0x106204 [0x01, 0xC0] (fun s => s.RIP = 0x106204) (addR32R32Effect 0x106204 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x106204 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x106204 0xc0 (by decide)) pre_rip
  have f715 : InstrSpec 0x106206 [0x31, 0xC8] (fun s => s.RIP = 0x106206) (xorR32R32Effect 0x106206 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106206 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106206 0xc8 (by decide)) pre_rip
  have f716 : InstrSpec 0x106208 [0x66, 0x89, 0x84, 0x24, 0xA2, 0x00, 0x00, 0x00] (StorePre 0x106208 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa2)) s (0x106208 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106208 8 0 (.sib 4 none 0 (.d32 0xa2)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106208 8 0 (.sib 4 none 0 (.d32 0xa2))).toInstrSpec (mov_m16_r16_effect_step 0x106208 0 (.sib 4 none 0 (.d32 0xa2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f717 : InstrSpec 0x106210 [0x0F, 0xB7, 0x84, 0x24, 0xA4, 0x00, 0x00, 0x00] (LoadPre 0x106210 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x106210 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106210 8 0 (.sib 4 none 0 (.d32 0xa4)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106210 8 0 (.sib 4 none 0 (.d32 0xa4))).toInstrSpec (movzx_r32_m16_effect_step 0x106210 0 (.sib 4 none 0 (.d32 0xa4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f718 : InstrSpec 0x106218 [0x89, 0xC1] (fun s => s.RIP = 0x106218) (movR32R32Effect 0x106218 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106218 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x106218 0xc1 (by decide)) pre_rip
  have f719 : InstrSpec 0x10621a [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x10621a) (shrR32Effect 0x10621a 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10621a 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x10621a 0xe9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1406) (RestInside.exec (n := 1406) (ρ' := [(0, 1404), (1, 1400), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061db) f700 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1407) (RestInside.out (n := 1407) f701 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1408) (ρ' := [(0, 1407), (1, 1400), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061e3) f701 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1409) (RestInside.out (n := 1409) f702 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1410) (ρ' := [(0, 1407), (1, 1409), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061e5) f702 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1411) (RestInside.out (n := 1411) f703 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1412) (ρ' := [(0, 1407), (1, 1411), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061e8) f703 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1413) (RestInside.out (n := 1413) f704 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1414) (ρ' := [(0, 1407), (1, 1413), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061ea) f704 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1415) (RestInside.out (n := 1415) f705 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1416) (ρ' := [(0, 1407), (1, 1415), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061f0) f705 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1417) (RestInside.out (n := 1417) f706 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1418) (ρ' := [(0, 1417), (1, 1415), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061f2) f706 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1419) (RestInside.out (n := 1419) f707 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1420) (ρ' := [(0, 1417), (1, 1419), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061f5) f707 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1421) (RestInside.out (n := 1421) f708 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1422) (ρ' := [(0, 1417), (1, 1421), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061f7) f708 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1423) (RestInside.out (n := 1423) f709 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1424) (ρ' := [(0, 1423), (1, 1421), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061f9) f709 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1425) (RestInside.out (n := 1425) f710 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1426) (ρ' := [(0, 1425), (1, 1421), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061fb) f710 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1427) (RestInside.out (n := 1427) f711 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1428) (ρ' := [(0, 1427), (1, 1421), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061fd) f711 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1429) (RestInside.out (n := 1429) f712 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1430) (ρ' := [(0, 1429), (1, 1421), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106202) f712 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1431) (RestInside.out (n := 1431) f713 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1432) (ρ' := [(0, 1429), (1, 1431), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106204) f713 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1433) (RestInside.out (n := 1433) f714 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1434) (ρ' := [(0, 1433), (1, 1431), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106206) f714 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1435) (RestInside.out (n := 1435) f715 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1436) (ρ' := [(0, 1435), (1, 1431), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106208) f715 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1437) (RestInside.exec (n := 1437) (ρ' := [(0, 1435), (1, 1431), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106210) f716 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1438) (RestInside.out (n := 1438) f717 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1439) (ρ' := [(0, 1438), (1, 1431), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106218) f717 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1440) (RestInside.out (n := 1440) f718 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1441) (ρ' := [(0, 1438), (1, 1440), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10621a) f718 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1442) (RestInside.out (n := 1442) f719 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1443) (ρ' := [(0, 1438), (1, 1442), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10621d) f719 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_36 code

theorem rest_l10593a_34 [Bindings] (code : CodeMap) :
    Rest (n := 1367) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1365), (1, 1359), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      512 0x106193 bytes_l10593a_34 b_l10593a_34 := by
  have f680 : InstrSpec 0x106193 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x106193) (andEaxImm32Effect 0x106193 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106193 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x106193 0x5050) pre_rip
  have f681 : InstrSpec 0x106198 [0x31, 0xC1] (fun s => s.RIP = 0x106198) (xorR32R32Effect 0x106198 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106198 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106198 0xc1 (by decide)) pre_rip
  have f682 : InstrSpec 0x10619a [0x01, 0xC0] (fun s => s.RIP = 0x10619a) (addR32R32Effect 0x10619a 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10619a 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x10619a 0xc0 (by decide)) pre_rip
  have f683 : InstrSpec 0x10619c [0x31, 0xC8] (fun s => s.RIP = 0x10619c) (xorR32R32Effect 0x10619c 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10619c 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10619c 0xc8 (by decide)) pre_rip
  have f684 : InstrSpec 0x10619e [0x66, 0x89, 0x84, 0x24, 0x9E, 0x00, 0x00, 0x00] (StorePre 0x10619e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9e)) s (0x10619e + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x10619e 8 0 (.sib 4 none 0 (.d32 0x9e)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10619e 8 0 (.sib 4 none 0 (.d32 0x9e))).toInstrSpec (mov_m16_r16_effect_step 0x10619e 0 (.sib 4 none 0 (.d32 0x9e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f685 : InstrSpec 0x1061a6 [0x0F, 0xB7, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x1061a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1061a6 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1061a6 8 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1061a6 8 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (movzx_r32_m16_effect_step 0x1061a6 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f686 : InstrSpec 0x1061ae [0x89, 0xC1] (fun s => s.RIP = 0x1061ae) (movR32R32Effect 0x1061ae 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1061ae 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1061ae 0xc1 (by decide)) pre_rip
  have f687 : InstrSpec 0x1061b0 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x1061b0) (shrR32Effect 0x1061b0 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1061b0 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x1061b0 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f688 : InstrSpec 0x1061b3 [0x31, 0xC1] (fun s => s.RIP = 0x1061b3) (xorR32R32Effect 0x1061b3 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1061b3 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1061b3 0xc1 (by decide)) pre_rip
  have f689 : InstrSpec 0x1061b5 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x1061b5) (andR32Imm32Effect 0x1061b5 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1061b5 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x1061b5 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f690 : InstrSpec 0x1061bb [0x31, 0xC8] (fun s => s.RIP = 0x1061bb) (xorR32R32Effect 0x1061bb 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1061bb 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1061bb 0xc8 (by decide)) pre_rip
  have f691 : InstrSpec 0x1061bd [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x1061bd) (shlR32Effect 0x1061bd 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x1061bd 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x1061bd 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f692 : InstrSpec 0x1061c0 [0x31, 0xC1] (fun s => s.RIP = 0x1061c0) (xorR32R32Effect 0x1061c0 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1061c0 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1061c0 0xc1 (by decide)) pre_rip
  have f693 : InstrSpec 0x1061c2 [0x89, 0xC8] (fun s => s.RIP = 0x1061c2) (movR32R32Effect 0x1061c2 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1061c2 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x1061c2 0xc8 (by decide)) pre_rip
  have f694 : InstrSpec 0x1061c4 [0xD1, 0xE8] (fun s => s.RIP = 0x1061c4) (shrR32Effect 0x1061c4 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x1061c4 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x1061c4 0xe8 (by decide) (by decide)) pre_rip
  have f695 : InstrSpec 0x1061c6 [0x31, 0xC8] (fun s => s.RIP = 0x1061c6) (xorR32R32Effect 0x1061c6 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1061c6 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1061c6 0xc8 (by decide)) pre_rip
  have f696 : InstrSpec 0x1061c8 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1061c8) (andEaxImm32Effect 0x1061c8 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x1061c8 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x1061c8 0x5050) pre_rip
  have f697 : InstrSpec 0x1061cd [0x31, 0xC1] (fun s => s.RIP = 0x1061cd) (xorR32R32Effect 0x1061cd 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1061cd 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1061cd 0xc1 (by decide)) pre_rip
  have f698 : InstrSpec 0x1061cf [0x01, 0xC0] (fun s => s.RIP = 0x1061cf) (addR32R32Effect 0x1061cf 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1061cf 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x1061cf 0xc0 (by decide)) pre_rip
  have f699 : InstrSpec 0x1061d1 [0x31, 0xC8] (fun s => s.RIP = 0x1061d1) (xorR32R32Effect 0x1061d1 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1061d1 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1061d1 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 1367) (RestInside.out (n := 1367) f680 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1368) (ρ' := [(0, 1367), (1, 1359), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106198) f680 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1369) (RestInside.out (n := 1369) f681 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1370) (ρ' := [(0, 1367), (1, 1369), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10619a) f681 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1371) (RestInside.out (n := 1371) f682 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1372) (ρ' := [(0, 1371), (1, 1369), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10619c) f682 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1373) (RestInside.out (n := 1373) f683 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1374) (ρ' := [(0, 1373), (1, 1369), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10619e) f683 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1375) (RestInside.exec (n := 1375) (ρ' := [(0, 1373), (1, 1369), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061a6) f684 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1376) (RestInside.out (n := 1376) f685 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1377) (ρ' := [(0, 1376), (1, 1369), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061ae) f685 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1378) (RestInside.out (n := 1378) f686 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1379) (ρ' := [(0, 1376), (1, 1378), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061b0) f686 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1380) (RestInside.out (n := 1380) f687 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1381) (ρ' := [(0, 1376), (1, 1380), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061b3) f687 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1382) (RestInside.out (n := 1382) f688 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1383) (ρ' := [(0, 1376), (1, 1382), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061b5) f688 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1384) (RestInside.out (n := 1384) f689 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1385) (ρ' := [(0, 1376), (1, 1384), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061bb) f689 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1386) (RestInside.out (n := 1386) f690 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1387) (ρ' := [(0, 1386), (1, 1384), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061bd) f690 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1388) (RestInside.out (n := 1388) f691 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1389) (ρ' := [(0, 1386), (1, 1388), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061c0) f691 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1390) (RestInside.out (n := 1390) f692 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1391) (ρ' := [(0, 1386), (1, 1390), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061c2) f692 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1392) (RestInside.out (n := 1392) f693 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1393) (ρ' := [(0, 1392), (1, 1390), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061c4) f693 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1394) (RestInside.out (n := 1394) f694 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1395) (ρ' := [(0, 1394), (1, 1390), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061c6) f694 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1396) (RestInside.out (n := 1396) f695 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1397) (ρ' := [(0, 1396), (1, 1390), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061c8) f695 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1398) (RestInside.out (n := 1398) f696 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1399) (ρ' := [(0, 1398), (1, 1390), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061cd) f696 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1400) (RestInside.out (n := 1400) f697 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1401) (ρ' := [(0, 1398), (1, 1400), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061cf) f697 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1402) (RestInside.out (n := 1402) f698 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1403) (ρ' := [(0, 1402), (1, 1400), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061d1) f698 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1404) (RestInside.out (n := 1404) f699 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1405) (ρ' := [(0, 1404), (1, 1400), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061d3) f699 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_35 code

theorem rest_l10593a_33 [Bindings] (code : CodeMap) :
    Rest (n := 1327) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1325), (1, 1323), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      532 0x106153 bytes_l10593a_33 b_l10593a_33 := by
  have f660 : InstrSpec 0x106153 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x106153) (shlR32Effect 0x106153 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x106153 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x106153 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f661 : InstrSpec 0x106156 [0x31, 0xC1] (fun s => s.RIP = 0x106156) (xorR32R32Effect 0x106156 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106156 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106156 0xc1 (by decide)) pre_rip
  have f662 : InstrSpec 0x106158 [0x41, 0x89, 0xCC] (fun s => s.RIP = 0x106158) (movR32R32Effect 0x106158 3 12 1)
      [.gpr 1] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x106158 3 12 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x106158 0x41 0xcc (by decide) (by decide)) pre_rip
  have f663 : InstrSpec 0x10615b [0x41, 0xD1, 0xEC] (fun s => s.RIP = 0x10615b) (shrR32Effect 0x10615b 3 12 1)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR32Effect_footprint 0x10615b 3 12 1).toInstrSpec (shr_r32_one_rex_effect_step 0x10615b 0x41 0xec (by decide) (by decide) (by decide)) pre_rip
  have f664 : InstrSpec 0x10615e [0x41, 0x31, 0xCC] (fun s => s.RIP = 0x10615e) (xorR32R32Effect 0x10615e 3 12 1)
      [.gpr 12, .gpr 1] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10615e 3 12 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x10615e 0x41 0xcc (by decide) (by decide)) pre_rip
  have f665 : InstrSpec 0x106161 [0x41, 0x81, 0xE4, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x106161) (andR32Imm32Effect 0x106161 7 12 0x5050)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106161 7 12 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x106161 0x41 0xe4 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f666 : InstrSpec 0x106168 [0x44, 0x31, 0xE1] (fun s => s.RIP = 0x106168) (xorR32R32Effect 0x106168 3 1 12)
      [.gpr 1, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106168 3 1 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x106168 0x44 0xe1 (by decide) (by decide)) pre_rip
  have f667 : InstrSpec 0x10616b [0x45, 0x01, 0xE4] (fun s => s.RIP = 0x10616b) (addR32R32Effect 0x10616b 3 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10616b 3 12 12).toInstrSpec (add_r32_r32_rex_effect_step 0x10616b 0x45 0xe4 (by decide) (by decide)) pre_rip
  have f668 : InstrSpec 0x10616e [0x41, 0x31, 0xCC] (fun s => s.RIP = 0x10616e) (xorR32R32Effect 0x10616e 3 12 1)
      [.gpr 12, .gpr 1] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10616e 3 12 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x10616e 0x41 0xcc (by decide) (by decide)) pre_rip
  have f669 : InstrSpec 0x106171 [0x0F, 0xB7, 0x84, 0x24, 0x9E, 0x00, 0x00, 0x00] (LoadPre 0x106171 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9e)) s (0x106171 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106171 8 0 (.sib 4 none 0 (.d32 0x9e)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106171 8 0 (.sib 4 none 0 (.d32 0x9e))).toInstrSpec (movzx_r32_m16_effect_step 0x106171 0 (.sib 4 none 0 (.d32 0x9e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f670 : InstrSpec 0x106179 [0x89, 0xC1] (fun s => s.RIP = 0x106179) (movR32R32Effect 0x106179 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106179 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x106179 0xc1 (by decide)) pre_rip
  have f671 : InstrSpec 0x10617b [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x10617b) (shrR32Effect 0x10617b 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10617b 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x10617b 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f672 : InstrSpec 0x10617e [0x31, 0xC1] (fun s => s.RIP = 0x10617e) (xorR32R32Effect 0x10617e 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10617e 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10617e 0xc1 (by decide)) pre_rip
  have f673 : InstrSpec 0x106180 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x106180) (andR32Imm32Effect 0x106180 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106180 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x106180 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f674 : InstrSpec 0x106186 [0x31, 0xC8] (fun s => s.RIP = 0x106186) (xorR32R32Effect 0x106186 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106186 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106186 0xc8 (by decide)) pre_rip
  have f675 : InstrSpec 0x106188 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x106188) (shlR32Effect 0x106188 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x106188 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x106188 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f676 : InstrSpec 0x10618b [0x31, 0xC1] (fun s => s.RIP = 0x10618b) (xorR32R32Effect 0x10618b 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10618b 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10618b 0xc1 (by decide)) pre_rip
  have f677 : InstrSpec 0x10618d [0x89, 0xC8] (fun s => s.RIP = 0x10618d) (movR32R32Effect 0x10618d 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x10618d 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x10618d 0xc8 (by decide)) pre_rip
  have f678 : InstrSpec 0x10618f [0xD1, 0xE8] (fun s => s.RIP = 0x10618f) (shrR32Effect 0x10618f 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x10618f 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x10618f 0xe8 (by decide) (by decide)) pre_rip
  have f679 : InstrSpec 0x106191 [0x31, 0xC8] (fun s => s.RIP = 0x106191) (xorR32R32Effect 0x106191 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106191 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106191 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 1327) (RestInside.out (n := 1327) f660 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1328) (ρ' := [(0, 1325), (1, 1327), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106156) f660 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1329) (RestInside.out (n := 1329) f661 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1330) (ρ' := [(0, 1325), (1, 1329), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106158) f661 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1331) (RestInside.out (n := 1331) f662 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1332) (ρ' := [(0, 1325), (1, 1329), (4, 4), (9, 1033), (12, 1331), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10615b) f662 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1333) (RestInside.out (n := 1333) f663 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1334) (ρ' := [(0, 1325), (1, 1329), (4, 4), (9, 1033), (12, 1333), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10615e) f663 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1335) (RestInside.out (n := 1335) f664 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1336) (ρ' := [(0, 1325), (1, 1329), (4, 4), (9, 1033), (12, 1335), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106161) f664 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1337) (RestInside.out (n := 1337) f665 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1338) (ρ' := [(0, 1325), (1, 1329), (4, 4), (9, 1033), (12, 1337), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106168) f665 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1339) (RestInside.out (n := 1339) f666 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1340) (ρ' := [(0, 1325), (1, 1339), (4, 4), (9, 1033), (12, 1337), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10616b) f666 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1341) (RestInside.out (n := 1341) f667 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1342) (ρ' := [(0, 1325), (1, 1339), (4, 4), (9, 1033), (12, 1341), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10616e) f667 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1343) (RestInside.out (n := 1343) f668 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1344) (ρ' := [(0, 1325), (1, 1339), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106171) f668 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1345) (RestInside.out (n := 1345) f669 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1346) (ρ' := [(0, 1345), (1, 1339), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106179) f669 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1347) (RestInside.out (n := 1347) f670 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1348) (ρ' := [(0, 1345), (1, 1347), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10617b) f670 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1349) (RestInside.out (n := 1349) f671 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1350) (ρ' := [(0, 1345), (1, 1349), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10617e) f671 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1351) (RestInside.out (n := 1351) f672 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1352) (ρ' := [(0, 1345), (1, 1351), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106180) f672 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1353) (RestInside.out (n := 1353) f673 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1354) (ρ' := [(0, 1345), (1, 1353), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106186) f673 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1355) (RestInside.out (n := 1355) f674 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1356) (ρ' := [(0, 1355), (1, 1353), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106188) f674 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1357) (RestInside.out (n := 1357) f675 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1358) (ρ' := [(0, 1355), (1, 1357), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10618b) f675 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1359) (RestInside.out (n := 1359) f676 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1360) (ρ' := [(0, 1355), (1, 1359), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10618d) f676 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1361) (RestInside.out (n := 1361) f677 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1362) (ρ' := [(0, 1361), (1, 1359), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10618f) f677 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1363) (RestInside.out (n := 1363) f678 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1364) (ρ' := [(0, 1363), (1, 1359), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106191) f678 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1365) (RestInside.out (n := 1365) f679 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1366) (ρ' := [(0, 1365), (1, 1359), (4, 4), (9, 1033), (12, 1343), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106193) f679 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_34 code

theorem rest_l10593a_32 [Bindings] (code : CodeMap) :
    Rest (n := 1288) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1284), (1, 1286), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      552 0x106111 bytes_l10593a_32 b_l10593a_32 := by
  have f640 : InstrSpec 0x106111 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x106111) (shrR32Effect 0x106111 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x106111 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x106111 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f641 : InstrSpec 0x106114 [0x31, 0xC1] (fun s => s.RIP = 0x106114) (xorR32R32Effect 0x106114 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106114 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106114 0xc1 (by decide)) pre_rip
  have f642 : InstrSpec 0x106116 [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x106116) (andR32Imm32Effect 0x106116 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106116 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x106116 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f643 : InstrSpec 0x10611c [0x31, 0xC8] (fun s => s.RIP = 0x10611c) (xorR32R32Effect 0x10611c 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10611c 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10611c 0xc8 (by decide)) pre_rip
  have f644 : InstrSpec 0x10611e [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x10611e) (shlR32Effect 0x10611e 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10611e 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x10611e 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f645 : InstrSpec 0x106121 [0x31, 0xC1] (fun s => s.RIP = 0x106121) (xorR32R32Effect 0x106121 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106121 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106121 0xc1 (by decide)) pre_rip
  have f646 : InstrSpec 0x106123 [0x89, 0xC8] (fun s => s.RIP = 0x106123) (movR32R32Effect 0x106123 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106123 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x106123 0xc8 (by decide)) pre_rip
  have f647 : InstrSpec 0x106125 [0xD1, 0xE8] (fun s => s.RIP = 0x106125) (shrR32Effect 0x106125 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x106125 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x106125 0xe8 (by decide) (by decide)) pre_rip
  have f648 : InstrSpec 0x106127 [0x31, 0xC8] (fun s => s.RIP = 0x106127) (xorR32R32Effect 0x106127 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106127 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106127 0xc8 (by decide)) pre_rip
  have f649 : InstrSpec 0x106129 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x106129) (andEaxImm32Effect 0x106129 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106129 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x106129 0x5050) pre_rip
  have f650 : InstrSpec 0x10612e [0x31, 0xC1] (fun s => s.RIP = 0x10612e) (xorR32R32Effect 0x10612e 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10612e 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10612e 0xc1 (by decide)) pre_rip
  have f651 : InstrSpec 0x106130 [0x01, 0xC0] (fun s => s.RIP = 0x106130) (addR32R32Effect 0x106130 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x106130 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x106130 0xc0 (by decide)) pre_rip
  have f652 : InstrSpec 0x106132 [0x31, 0xC8] (fun s => s.RIP = 0x106132) (xorR32R32Effect 0x106132 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106132 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106132 0xc8 (by decide)) pre_rip
  have f653 : InstrSpec 0x106134 [0x66, 0x89, 0x84, 0x24, 0x8A, 0x00, 0x00, 0x00] (StorePre 0x106134 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8a)) s (0x106134 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106134 8 0 (.sib 4 none 0 (.d32 0x8a)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106134 8 0 (.sib 4 none 0 (.d32 0x8a))).toInstrSpec (mov_m16_r16_effect_step 0x106134 0 (.sib 4 none 0 (.d32 0x8a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f654 : InstrSpec 0x10613c [0x0F, 0xB7, 0x84, 0x24, 0x9C, 0x00, 0x00, 0x00] (LoadPre 0x10613c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x10613c + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x10613c 8 0 (.sib 4 none 0 (.d32 0x9c)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10613c 8 0 (.sib 4 none 0 (.d32 0x9c))).toInstrSpec (movzx_r32_m16_effect_step 0x10613c 0 (.sib 4 none 0 (.d32 0x9c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f655 : InstrSpec 0x106144 [0x89, 0xC1] (fun s => s.RIP = 0x106144) (movR32R32Effect 0x106144 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106144 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x106144 0xc1 (by decide)) pre_rip
  have f656 : InstrSpec 0x106146 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x106146) (shrR32Effect 0x106146 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x106146 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x106146 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f657 : InstrSpec 0x106149 [0x31, 0xC1] (fun s => s.RIP = 0x106149) (xorR32R32Effect 0x106149 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106149 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106149 0xc1 (by decide)) pre_rip
  have f658 : InstrSpec 0x10614b [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x10614b) (andR32Imm32Effect 0x10614b 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10614b 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x10614b 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f659 : InstrSpec 0x106151 [0x31, 0xC8] (fun s => s.RIP = 0x106151) (xorR32R32Effect 0x106151 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106151 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106151 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 1288) (RestInside.out (n := 1288) f640 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1289) (ρ' := [(0, 1284), (1, 1288), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106114) f640 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1290) (RestInside.out (n := 1290) f641 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1291) (ρ' := [(0, 1284), (1, 1290), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106116) f641 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1292) (RestInside.out (n := 1292) f642 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1293) (ρ' := [(0, 1284), (1, 1292), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10611c) f642 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1294) (RestInside.out (n := 1294) f643 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1295) (ρ' := [(0, 1294), (1, 1292), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10611e) f643 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1296) (RestInside.out (n := 1296) f644 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1297) (ρ' := [(0, 1294), (1, 1296), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106121) f644 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1298) (RestInside.out (n := 1298) f645 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1299) (ρ' := [(0, 1294), (1, 1298), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106123) f645 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1300) (RestInside.out (n := 1300) f646 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1301) (ρ' := [(0, 1300), (1, 1298), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106125) f646 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1302) (RestInside.out (n := 1302) f647 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1303) (ρ' := [(0, 1302), (1, 1298), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106127) f647 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1304) (RestInside.out (n := 1304) f648 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1305) (ρ' := [(0, 1304), (1, 1298), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106129) f648 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1306) (RestInside.out (n := 1306) f649 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1307) (ρ' := [(0, 1306), (1, 1298), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10612e) f649 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1308) (RestInside.out (n := 1308) f650 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1309) (ρ' := [(0, 1306), (1, 1308), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106130) f650 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1310) (RestInside.out (n := 1310) f651 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1311) (ρ' := [(0, 1310), (1, 1308), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106132) f651 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1312) (RestInside.out (n := 1312) f652 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1313) (ρ' := [(0, 1312), (1, 1308), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106134) f652 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1314) (RestInside.exec (n := 1314) (ρ' := [(0, 1312), (1, 1308), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10613c) f653 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1315) (RestInside.out (n := 1315) f654 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1316) (ρ' := [(0, 1315), (1, 1308), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106144) f654 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1317) (RestInside.out (n := 1317) f655 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1318) (ρ' := [(0, 1315), (1, 1317), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106146) f655 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1319) (RestInside.out (n := 1319) f656 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1320) (ρ' := [(0, 1315), (1, 1319), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106149) f656 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1321) (RestInside.out (n := 1321) f657 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1322) (ρ' := [(0, 1315), (1, 1321), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10614b) f657 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1323) (RestInside.out (n := 1323) f658 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1324) (ρ' := [(0, 1315), (1, 1323), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106151) f658 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1325) (RestInside.out (n := 1325) f659 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1326) (ρ' := [(0, 1325), (1, 1323), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106153) f659 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_33 code

theorem rest_l10593a_31 [Bindings] (code : CodeMap) :
    Rest (n := 1250) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1248), (1, 1246), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      572 0x1060c8 bytes_l10593a_31 b_l10593a_31 := by
  have f620 : InstrSpec 0x1060c8 [0x31, 0xC8] (fun s => s.RIP = 0x1060c8) (xorR32R32Effect 0x1060c8 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1060c8 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1060c8 0xc8 (by decide)) pre_rip
  have f621 : InstrSpec 0x1060ca [0x66, 0x89, 0x84, 0x24, 0x86, 0x00, 0x00, 0x00] (StorePre 0x1060ca 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x86)) s (0x1060ca + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1060ca 8 0 (.sib 4 none 0 (.d32 0x86)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1060ca 8 0 (.sib 4 none 0 (.d32 0x86))).toInstrSpec (mov_m16_r16_effect_step 0x1060ca 0 (.sib 4 none 0 (.d32 0x86)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f622 : InstrSpec 0x1060d2 [0x0F, 0xB7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x1060d2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1060d2 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1060d2 8 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1060d2 8 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (movzx_r32_m16_effect_step 0x1060d2 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f623 : InstrSpec 0x1060da [0x89, 0xC1] (fun s => s.RIP = 0x1060da) (movR32R32Effect 0x1060da 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1060da 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1060da 0xc1 (by decide)) pre_rip
  have f624 : InstrSpec 0x1060dc [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x1060dc) (shrR32Effect 0x1060dc 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1060dc 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x1060dc 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f625 : InstrSpec 0x1060df [0x31, 0xC1] (fun s => s.RIP = 0x1060df) (xorR32R32Effect 0x1060df 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1060df 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1060df 0xc1 (by decide)) pre_rip
  have f626 : InstrSpec 0x1060e1 [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x1060e1) (andR32Imm32Effect 0x1060e1 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1060e1 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x1060e1 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f627 : InstrSpec 0x1060e7 [0x31, 0xC8] (fun s => s.RIP = 0x1060e7) (xorR32R32Effect 0x1060e7 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1060e7 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1060e7 0xc8 (by decide)) pre_rip
  have f628 : InstrSpec 0x1060e9 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x1060e9) (shlR32Effect 0x1060e9 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x1060e9 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x1060e9 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f629 : InstrSpec 0x1060ec [0x31, 0xC1] (fun s => s.RIP = 0x1060ec) (xorR32R32Effect 0x1060ec 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1060ec 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1060ec 0xc1 (by decide)) pre_rip
  have f630 : InstrSpec 0x1060ee [0x89, 0xC8] (fun s => s.RIP = 0x1060ee) (movR32R32Effect 0x1060ee 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1060ee 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x1060ee 0xc8 (by decide)) pre_rip
  have f631 : InstrSpec 0x1060f0 [0xD1, 0xE8] (fun s => s.RIP = 0x1060f0) (shrR32Effect 0x1060f0 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x1060f0 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x1060f0 0xe8 (by decide) (by decide)) pre_rip
  have f632 : InstrSpec 0x1060f2 [0x31, 0xC8] (fun s => s.RIP = 0x1060f2) (xorR32R32Effect 0x1060f2 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1060f2 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1060f2 0xc8 (by decide)) pre_rip
  have f633 : InstrSpec 0x1060f4 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1060f4) (andEaxImm32Effect 0x1060f4 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x1060f4 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x1060f4 0x5050) pre_rip
  have f634 : InstrSpec 0x1060f9 [0x31, 0xC1] (fun s => s.RIP = 0x1060f9) (xorR32R32Effect 0x1060f9 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1060f9 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1060f9 0xc1 (by decide)) pre_rip
  have f635 : InstrSpec 0x1060fb [0x01, 0xC0] (fun s => s.RIP = 0x1060fb) (addR32R32Effect 0x1060fb 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1060fb 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x1060fb 0xc0 (by decide)) pre_rip
  have f636 : InstrSpec 0x1060fd [0x31, 0xC8] (fun s => s.RIP = 0x1060fd) (xorR32R32Effect 0x1060fd 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1060fd 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1060fd 0xc8 (by decide)) pre_rip
  have f637 : InstrSpec 0x1060ff [0x66, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1060ff 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1060ff + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1060ff 8 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1060ff 8 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m16_r16_effect_step 0x1060ff 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f638 : InstrSpec 0x106107 [0x0F, 0xB7, 0x84, 0x24, 0x8A, 0x00, 0x00, 0x00] (LoadPre 0x106107 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8a)) s (0x106107 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106107 8 0 (.sib 4 none 0 (.d32 0x8a)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106107 8 0 (.sib 4 none 0 (.d32 0x8a))).toInstrSpec (movzx_r32_m16_effect_step 0x106107 0 (.sib 4 none 0 (.d32 0x8a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f639 : InstrSpec 0x10610f [0x89, 0xC1] (fun s => s.RIP = 0x10610f) (movR32R32Effect 0x10610f 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10610f 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x10610f 0xc1 (by decide)) pre_rip
  refine Rest.ofInside (n := 1250) (RestInside.out (n := 1250) f620 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1251) (ρ' := [(0, 1250), (1, 1246), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060ca) f620 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1252) (RestInside.exec (n := 1252) (ρ' := [(0, 1250), (1, 1246), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060d2) f621 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1253) (RestInside.out (n := 1253) f622 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1254) (ρ' := [(0, 1253), (1, 1246), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060da) f622 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1255) (RestInside.out (n := 1255) f623 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1256) (ρ' := [(0, 1253), (1, 1255), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060dc) f623 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1257) (RestInside.out (n := 1257) f624 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1258) (ρ' := [(0, 1253), (1, 1257), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060df) f624 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1259) (RestInside.out (n := 1259) f625 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1260) (ρ' := [(0, 1253), (1, 1259), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060e1) f625 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1261) (RestInside.out (n := 1261) f626 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1262) (ρ' := [(0, 1253), (1, 1261), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060e7) f626 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1263) (RestInside.out (n := 1263) f627 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1264) (ρ' := [(0, 1263), (1, 1261), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060e9) f627 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1265) (RestInside.out (n := 1265) f628 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1266) (ρ' := [(0, 1263), (1, 1265), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060ec) f628 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1267) (RestInside.out (n := 1267) f629 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1268) (ρ' := [(0, 1263), (1, 1267), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060ee) f629 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1269) (RestInside.out (n := 1269) f630 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1270) (ρ' := [(0, 1269), (1, 1267), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060f0) f630 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1271) (RestInside.out (n := 1271) f631 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1272) (ρ' := [(0, 1271), (1, 1267), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060f2) f631 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1273) (RestInside.out (n := 1273) f632 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1274) (ρ' := [(0, 1273), (1, 1267), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060f4) f632 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1275) (RestInside.out (n := 1275) f633 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1276) (ρ' := [(0, 1275), (1, 1267), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060f9) f633 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1277) (RestInside.out (n := 1277) f634 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1278) (ρ' := [(0, 1275), (1, 1277), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060fb) f634 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1279) (RestInside.out (n := 1279) f635 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1280) (ρ' := [(0, 1279), (1, 1277), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060fd) f635 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1281) (RestInside.out (n := 1281) f636 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1282) (ρ' := [(0, 1281), (1, 1277), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060ff) f636 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1283) (RestInside.exec (n := 1283) (ρ' := [(0, 1281), (1, 1277), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106107) f637 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1284) (RestInside.out (n := 1284) f638 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1285) (ρ' := [(0, 1284), (1, 1277), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10610f) f638 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1286) (RestInside.out (n := 1286) f639 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1287) (ρ' := [(0, 1284), (1, 1286), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106111) f639 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_32 code

theorem rest_l10593a_30 [Bindings] (code : CodeMap) :
    Rest (n := 1211) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1209), (1, 1205), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      592 0x106088 bytes_l10593a_30 b_l10593a_30 := by
  have f600 : InstrSpec 0x106088 [0x31, 0xC8] (fun s => s.RIP = 0x106088) (xorR32R32Effect 0x106088 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106088 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106088 0xc8 (by decide)) pre_rip
  have f601 : InstrSpec 0x10608a [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x10608a) (andEaxImm32Effect 0x10608a 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x10608a 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x10608a 0x5050) pre_rip
  have f602 : InstrSpec 0x10608f [0x31, 0xC1] (fun s => s.RIP = 0x10608f) (xorR32R32Effect 0x10608f 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10608f 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10608f 0xc1 (by decide)) pre_rip
  have f603 : InstrSpec 0x106091 [0x01, 0xC0] (fun s => s.RIP = 0x106091) (addR32R32Effect 0x106091 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x106091 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x106091 0xc0 (by decide)) pre_rip
  have f604 : InstrSpec 0x106093 [0x31, 0xC8] (fun s => s.RIP = 0x106093) (xorR32R32Effect 0x106093 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106093 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106093 0xc8 (by decide)) pre_rip
  have f605 : InstrSpec 0x106095 [0x66, 0x89, 0x84, 0x24, 0x84, 0x00, 0x00, 0x00] (StorePre 0x106095 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x106095 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106095 8 0 (.sib 4 none 0 (.d32 0x84)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106095 8 0 (.sib 4 none 0 (.d32 0x84))).toInstrSpec (mov_m16_r16_effect_step 0x106095 0 (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f606 : InstrSpec 0x10609d [0x0F, 0xB7, 0x84, 0x24, 0x86, 0x00, 0x00, 0x00] (LoadPre 0x10609d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x86)) s (0x10609d + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x10609d 8 0 (.sib 4 none 0 (.d32 0x86)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10609d 8 0 (.sib 4 none 0 (.d32 0x86))).toInstrSpec (movzx_r32_m16_effect_step 0x10609d 0 (.sib 4 none 0 (.d32 0x86)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f607 : InstrSpec 0x1060a5 [0x89, 0xC1] (fun s => s.RIP = 0x1060a5) (movR32R32Effect 0x1060a5 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1060a5 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1060a5 0xc1 (by decide)) pre_rip
  have f608 : InstrSpec 0x1060a7 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x1060a7) (shrR32Effect 0x1060a7 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1060a7 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x1060a7 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f609 : InstrSpec 0x1060aa [0x31, 0xC1] (fun s => s.RIP = 0x1060aa) (xorR32R32Effect 0x1060aa 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1060aa 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1060aa 0xc1 (by decide)) pre_rip
  have f610 : InstrSpec 0x1060ac [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x1060ac) (andR32Imm32Effect 0x1060ac 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1060ac 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x1060ac 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f611 : InstrSpec 0x1060b2 [0x31, 0xC8] (fun s => s.RIP = 0x1060b2) (xorR32R32Effect 0x1060b2 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1060b2 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1060b2 0xc8 (by decide)) pre_rip
  have f612 : InstrSpec 0x1060b4 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x1060b4) (shlR32Effect 0x1060b4 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x1060b4 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x1060b4 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f613 : InstrSpec 0x1060b7 [0x31, 0xC1] (fun s => s.RIP = 0x1060b7) (xorR32R32Effect 0x1060b7 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1060b7 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1060b7 0xc1 (by decide)) pre_rip
  have f614 : InstrSpec 0x1060b9 [0x89, 0xC8] (fun s => s.RIP = 0x1060b9) (movR32R32Effect 0x1060b9 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1060b9 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x1060b9 0xc8 (by decide)) pre_rip
  have f615 : InstrSpec 0x1060bb [0xD1, 0xE8] (fun s => s.RIP = 0x1060bb) (shrR32Effect 0x1060bb 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x1060bb 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x1060bb 0xe8 (by decide) (by decide)) pre_rip
  have f616 : InstrSpec 0x1060bd [0x31, 0xC8] (fun s => s.RIP = 0x1060bd) (xorR32R32Effect 0x1060bd 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1060bd 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1060bd 0xc8 (by decide)) pre_rip
  have f617 : InstrSpec 0x1060bf [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1060bf) (andEaxImm32Effect 0x1060bf 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x1060bf 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x1060bf 0x5050) pre_rip
  have f618 : InstrSpec 0x1060c4 [0x31, 0xC1] (fun s => s.RIP = 0x1060c4) (xorR32R32Effect 0x1060c4 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1060c4 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1060c4 0xc1 (by decide)) pre_rip
  have f619 : InstrSpec 0x1060c6 [0x01, 0xC0] (fun s => s.RIP = 0x1060c6) (addR32R32Effect 0x1060c6 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1060c6 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x1060c6 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 1211) (RestInside.out (n := 1211) f600 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1212) (ρ' := [(0, 1211), (1, 1205), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10608a) f600 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1213) (RestInside.out (n := 1213) f601 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1214) (ρ' := [(0, 1213), (1, 1205), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10608f) f601 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1215) (RestInside.out (n := 1215) f602 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1216) (ρ' := [(0, 1213), (1, 1215), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106091) f602 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1217) (RestInside.out (n := 1217) f603 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1218) (ρ' := [(0, 1217), (1, 1215), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106093) f603 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1219) (RestInside.out (n := 1219) f604 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1220) (ρ' := [(0, 1219), (1, 1215), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106095) f604 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1221) (RestInside.exec (n := 1221) (ρ' := [(0, 1219), (1, 1215), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10609d) f605 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1222) (RestInside.out (n := 1222) f606 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1223) (ρ' := [(0, 1222), (1, 1215), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060a5) f606 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1224) (RestInside.out (n := 1224) f607 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1225) (ρ' := [(0, 1222), (1, 1224), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060a7) f607 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1226) (RestInside.out (n := 1226) f608 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1227) (ρ' := [(0, 1222), (1, 1226), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060aa) f608 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1228) (RestInside.out (n := 1228) f609 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1229) (ρ' := [(0, 1222), (1, 1228), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060ac) f609 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1230) (RestInside.out (n := 1230) f610 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1231) (ρ' := [(0, 1222), (1, 1230), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060b2) f610 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1232) (RestInside.out (n := 1232) f611 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1233) (ρ' := [(0, 1232), (1, 1230), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060b4) f611 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1234) (RestInside.out (n := 1234) f612 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1235) (ρ' := [(0, 1232), (1, 1234), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060b7) f612 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1236) (RestInside.out (n := 1236) f613 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1237) (ρ' := [(0, 1232), (1, 1236), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060b9) f613 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1238) (RestInside.out (n := 1238) f614 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1239) (ρ' := [(0, 1238), (1, 1236), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060bb) f614 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1240) (RestInside.out (n := 1240) f615 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1241) (ρ' := [(0, 1240), (1, 1236), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060bd) f615 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1242) (RestInside.out (n := 1242) f616 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1243) (ρ' := [(0, 1242), (1, 1236), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060bf) f616 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1244) (RestInside.out (n := 1244) f617 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1245) (ρ' := [(0, 1244), (1, 1236), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060c4) f617 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1246) (RestInside.out (n := 1246) f618 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1247) (ρ' := [(0, 1244), (1, 1246), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060c6) f618 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1248) (RestInside.out (n := 1248) f619 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1249) (ρ' := [(0, 1248), (1, 1246), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060c8) f619 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_31 code

theorem rest_l10593a_29 [Bindings] (code : CodeMap) :
    Rest (n := 1172) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1170), (1, 1168), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      612 0x10604a bytes_l10593a_29 b_l10593a_29 := by
  have f580 : InstrSpec 0x10604a [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x10604a) (shlR32Effect 0x10604a 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10604a 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x10604a 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f581 : InstrSpec 0x10604d [0x31, 0xC1] (fun s => s.RIP = 0x10604d) (xorR32R32Effect 0x10604d 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10604d 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10604d 0xc1 (by decide)) pre_rip
  have f582 : InstrSpec 0x10604f [0x89, 0xC8] (fun s => s.RIP = 0x10604f) (movR32R32Effect 0x10604f 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x10604f 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x10604f 0xc8 (by decide)) pre_rip
  have f583 : InstrSpec 0x106051 [0xD1, 0xE8] (fun s => s.RIP = 0x106051) (shrR32Effect 0x106051 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x106051 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x106051 0xe8 (by decide) (by decide)) pre_rip
  have f584 : InstrSpec 0x106053 [0x31, 0xC8] (fun s => s.RIP = 0x106053) (xorR32R32Effect 0x106053 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106053 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106053 0xc8 (by decide)) pre_rip
  have f585 : InstrSpec 0x106055 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x106055) (andEaxImm32Effect 0x106055 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106055 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x106055 0x5050) pre_rip
  have f586 : InstrSpec 0x10605a [0x31, 0xC1] (fun s => s.RIP = 0x10605a) (xorR32R32Effect 0x10605a 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10605a 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10605a 0xc1 (by decide)) pre_rip
  have f587 : InstrSpec 0x10605c [0x01, 0xC0] (fun s => s.RIP = 0x10605c) (addR32R32Effect 0x10605c 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10605c 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x10605c 0xc0 (by decide)) pre_rip
  have f588 : InstrSpec 0x10605e [0x31, 0xC8] (fun s => s.RIP = 0x10605e) (xorR32R32Effect 0x10605e 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10605e 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10605e 0xc8 (by decide)) pre_rip
  have f589 : InstrSpec 0x106060 [0x66, 0x89, 0x84, 0x24, 0x82, 0x00, 0x00, 0x00] (StorePre 0x106060 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x82)) s (0x106060 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106060 8 0 (.sib 4 none 0 (.d32 0x82)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106060 8 0 (.sib 4 none 0 (.d32 0x82))).toInstrSpec (mov_m16_r16_effect_step 0x106060 0 (.sib 4 none 0 (.d32 0x82)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f590 : InstrSpec 0x106068 [0x0F, 0xB7, 0x84, 0x24, 0x84, 0x00, 0x00, 0x00] (LoadPre 0x106068 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x106068 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106068 8 0 (.sib 4 none 0 (.d32 0x84)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106068 8 0 (.sib 4 none 0 (.d32 0x84))).toInstrSpec (movzx_r32_m16_effect_step 0x106068 0 (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f591 : InstrSpec 0x106070 [0x89, 0xC1] (fun s => s.RIP = 0x106070) (movR32R32Effect 0x106070 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106070 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x106070 0xc1 (by decide)) pre_rip
  have f592 : InstrSpec 0x106072 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x106072) (shrR32Effect 0x106072 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x106072 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x106072 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f593 : InstrSpec 0x106075 [0x31, 0xC1] (fun s => s.RIP = 0x106075) (xorR32R32Effect 0x106075 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106075 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106075 0xc1 (by decide)) pre_rip
  have f594 : InstrSpec 0x106077 [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x106077) (andR32Imm32Effect 0x106077 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106077 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x106077 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f595 : InstrSpec 0x10607d [0x31, 0xC8] (fun s => s.RIP = 0x10607d) (xorR32R32Effect 0x10607d 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10607d 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10607d 0xc8 (by decide)) pre_rip
  have f596 : InstrSpec 0x10607f [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x10607f) (shlR32Effect 0x10607f 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10607f 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x10607f 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f597 : InstrSpec 0x106082 [0x31, 0xC1] (fun s => s.RIP = 0x106082) (xorR32R32Effect 0x106082 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106082 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106082 0xc1 (by decide)) pre_rip
  have f598 : InstrSpec 0x106084 [0x89, 0xC8] (fun s => s.RIP = 0x106084) (movR32R32Effect 0x106084 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106084 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x106084 0xc8 (by decide)) pre_rip
  have f599 : InstrSpec 0x106086 [0xD1, 0xE8] (fun s => s.RIP = 0x106086) (shrR32Effect 0x106086 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x106086 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x106086 0xe8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1172) (RestInside.out (n := 1172) f580 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1173) (ρ' := [(0, 1170), (1, 1172), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10604d) f580 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1174) (RestInside.out (n := 1174) f581 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1175) (ρ' := [(0, 1170), (1, 1174), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10604f) f581 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1176) (RestInside.out (n := 1176) f582 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1177) (ρ' := [(0, 1176), (1, 1174), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106051) f582 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1178) (RestInside.out (n := 1178) f583 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1179) (ρ' := [(0, 1178), (1, 1174), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106053) f583 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1180) (RestInside.out (n := 1180) f584 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1181) (ρ' := [(0, 1180), (1, 1174), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106055) f584 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1182) (RestInside.out (n := 1182) f585 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1183) (ρ' := [(0, 1182), (1, 1174), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10605a) f585 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1184) (RestInside.out (n := 1184) f586 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1185) (ρ' := [(0, 1182), (1, 1184), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10605c) f586 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1186) (RestInside.out (n := 1186) f587 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1187) (ρ' := [(0, 1186), (1, 1184), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10605e) f587 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1188) (RestInside.out (n := 1188) f588 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1189) (ρ' := [(0, 1188), (1, 1184), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106060) f588 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1190) (RestInside.exec (n := 1190) (ρ' := [(0, 1188), (1, 1184), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106068) f589 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1191) (RestInside.out (n := 1191) f590 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1192) (ρ' := [(0, 1191), (1, 1184), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106070) f590 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1193) (RestInside.out (n := 1193) f591 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1194) (ρ' := [(0, 1191), (1, 1193), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106072) f591 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1195) (RestInside.out (n := 1195) f592 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1196) (ρ' := [(0, 1191), (1, 1195), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106075) f592 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1197) (RestInside.out (n := 1197) f593 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1198) (ρ' := [(0, 1191), (1, 1197), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106077) f593 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1199) (RestInside.out (n := 1199) f594 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1200) (ρ' := [(0, 1191), (1, 1199), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10607d) f594 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1201) (RestInside.out (n := 1201) f595 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1202) (ρ' := [(0, 1201), (1, 1199), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10607f) f595 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1203) (RestInside.out (n := 1203) f596 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1204) (ρ' := [(0, 1201), (1, 1203), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106082) f596 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1205) (RestInside.out (n := 1205) f597 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1206) (ρ' := [(0, 1201), (1, 1205), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106084) f597 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1207) (RestInside.out (n := 1207) f598 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1208) (ρ' := [(0, 1207), (1, 1205), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106086) f598 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1209) (RestInside.out (n := 1209) f599 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1210) (ρ' := [(0, 1209), (1, 1205), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106088) f599 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_30 code

theorem rest_l10593a_28 [Bindings] (code : CodeMap) :
    Rest (n := 1133) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1129), (1, 1131), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]
      632 0x106008 bytes_l10593a_28 b_l10593a_28 := by
  have f560 : InstrSpec 0x106008 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x106008) (shrR32Effect 0x106008 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x106008 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x106008 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f561 : InstrSpec 0x10600b [0x31, 0xC1] (fun s => s.RIP = 0x10600b) (xorR32R32Effect 0x10600b 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10600b 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10600b 0xc1 (by decide)) pre_rip
  have f562 : InstrSpec 0x10600d [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x10600d) (andR32Imm32Effect 0x10600d 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10600d 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x10600d 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f563 : InstrSpec 0x106013 [0x31, 0xC8] (fun s => s.RIP = 0x106013) (xorR32R32Effect 0x106013 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106013 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106013 0xc8 (by decide)) pre_rip
  have f564 : InstrSpec 0x106015 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x106015) (shlR32Effect 0x106015 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x106015 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x106015 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f565 : InstrSpec 0x106018 [0x31, 0xC1] (fun s => s.RIP = 0x106018) (xorR32R32Effect 0x106018 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106018 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106018 0xc1 (by decide)) pre_rip
  have f566 : InstrSpec 0x10601a [0x89, 0xC8] (fun s => s.RIP = 0x10601a) (movR32R32Effect 0x10601a 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x10601a 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x10601a 0xc8 (by decide)) pre_rip
  have f567 : InstrSpec 0x10601c [0xD1, 0xE8] (fun s => s.RIP = 0x10601c) (shrR32Effect 0x10601c 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x10601c 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x10601c 0xe8 (by decide) (by decide)) pre_rip
  have f568 : InstrSpec 0x10601e [0x31, 0xC8] (fun s => s.RIP = 0x10601e) (xorR32R32Effect 0x10601e 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10601e 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10601e 0xc8 (by decide)) pre_rip
  have f569 : InstrSpec 0x106020 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x106020) (andEaxImm32Effect 0x106020 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106020 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x106020 0x5050) pre_rip
  have f570 : InstrSpec 0x106025 [0x31, 0xC1] (fun s => s.RIP = 0x106025) (xorR32R32Effect 0x106025 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106025 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106025 0xc1 (by decide)) pre_rip
  have f571 : InstrSpec 0x106027 [0x01, 0xC0] (fun s => s.RIP = 0x106027) (addR32R32Effect 0x106027 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x106027 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x106027 0xc0 (by decide)) pre_rip
  have f572 : InstrSpec 0x106029 [0x31, 0xC8] (fun s => s.RIP = 0x106029) (xorR32R32Effect 0x106029 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106029 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106029 0xc8 (by decide)) pre_rip
  have f573 : InstrSpec 0x10602b [0x66, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x10602b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10602b + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x10602b 8 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10602b 8 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m16_r16_effect_step 0x10602b 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f574 : InstrSpec 0x106033 [0x0F, 0xB7, 0x84, 0x24, 0x82, 0x00, 0x00, 0x00] (LoadPre 0x106033 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x82)) s (0x106033 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106033 8 0 (.sib 4 none 0 (.d32 0x82)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106033 8 0 (.sib 4 none 0 (.d32 0x82))).toInstrSpec (movzx_r32_m16_effect_step 0x106033 0 (.sib 4 none 0 (.d32 0x82)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f575 : InstrSpec 0x10603b [0x89, 0xC1] (fun s => s.RIP = 0x10603b) (movR32R32Effect 0x10603b 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10603b 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x10603b 0xc1 (by decide)) pre_rip
  have f576 : InstrSpec 0x10603d [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x10603d) (shrR32Effect 0x10603d 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10603d 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x10603d 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f577 : InstrSpec 0x106040 [0x31, 0xC1] (fun s => s.RIP = 0x106040) (xorR32R32Effect 0x106040 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106040 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106040 0xc1 (by decide)) pre_rip
  have f578 : InstrSpec 0x106042 [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x106042) (andR32Imm32Effect 0x106042 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106042 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x106042 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f579 : InstrSpec 0x106048 [0x31, 0xC8] (fun s => s.RIP = 0x106048) (xorR32R32Effect 0x106048 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106048 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106048 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 1133) (RestInside.out (n := 1133) f560 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1134) (ρ' := [(0, 1129), (1, 1133), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10600b) f560 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1135) (RestInside.out (n := 1135) f561 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1136) (ρ' := [(0, 1129), (1, 1135), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10600d) f561 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1137) (RestInside.out (n := 1137) f562 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1138) (ρ' := [(0, 1129), (1, 1137), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106013) f562 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1139) (RestInside.out (n := 1139) f563 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1140) (ρ' := [(0, 1139), (1, 1137), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106015) f563 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1141) (RestInside.out (n := 1141) f564 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1142) (ρ' := [(0, 1139), (1, 1141), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106018) f564 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1143) (RestInside.out (n := 1143) f565 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1144) (ρ' := [(0, 1139), (1, 1143), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10601a) f565 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1145) (RestInside.out (n := 1145) f566 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1146) (ρ' := [(0, 1145), (1, 1143), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10601c) f566 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1147) (RestInside.out (n := 1147) f567 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1148) (ρ' := [(0, 1147), (1, 1143), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10601e) f567 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1149) (RestInside.out (n := 1149) f568 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1150) (ρ' := [(0, 1149), (1, 1143), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106020) f568 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1151) (RestInside.out (n := 1151) f569 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1152) (ρ' := [(0, 1151), (1, 1143), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106025) f569 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1153) (RestInside.out (n := 1153) f570 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1154) (ρ' := [(0, 1151), (1, 1153), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106027) f570 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1155) (RestInside.out (n := 1155) f571 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1156) (ρ' := [(0, 1155), (1, 1153), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106029) f571 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1157) (RestInside.out (n := 1157) f572 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1158) (ρ' := [(0, 1157), (1, 1153), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10602b) f572 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1159) (RestInside.exec (n := 1159) (ρ' := [(0, 1157), (1, 1153), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106033) f573 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1160) (RestInside.out (n := 1160) f574 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1161) (ρ' := [(0, 1160), (1, 1153), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10603b) f574 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1162) (RestInside.out (n := 1162) f575 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1163) (ρ' := [(0, 1160), (1, 1162), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10603d) f575 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1164) (RestInside.out (n := 1164) f576 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1165) (ρ' := [(0, 1160), (1, 1164), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106040) f576 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1166) (RestInside.out (n := 1166) f577 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1167) (ρ' := [(0, 1160), (1, 1166), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106042) f577 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1168) (RestInside.out (n := 1168) f578 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1169) (ρ' := [(0, 1160), (1, 1168), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106048) f578 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1170) (RestInside.out (n := 1170) f579 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1171) (ρ' := [(0, 1170), (1, 1168), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10604a) f579 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_29 code

theorem rest_l10593a_27 [Bindings] (code : CodeMap) :
    Rest (n := 1094) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1078), (1, 1092), (4, 4), (9, 1033), (14, 1049), (15, 1090), (22, 22), (39, 39), (50, 50), (51, 51)]
      652 0x105fc9 bytes_l10593a_27 b_l10593a_27 := by
  have f540 : InstrSpec 0x105fc9 [0x45, 0x01, 0xFF] (fun s => s.RIP = 0x105fc9) (addR32R32Effect 0x105fc9 3 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105fc9 3 15 15).toInstrSpec (add_r32_r32_rex_effect_step 0x105fc9 0x45 0xff (by decide) (by decide)) pre_rip
  have f541 : InstrSpec 0x105fcc [0x41, 0x31, 0xCF] (fun s => s.RIP = 0x105fcc) (xorR32R32Effect 0x105fcc 3 15 1)
      [.gpr 15, .gpr 1] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105fcc 3 15 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x105fcc 0x41 0xcf (by decide) (by decide)) pre_rip
  have f542 : InstrSpec 0x105fcf [0x0F, 0xB7, 0x44, 0x24, 0x7E] (LoadPre 0x105fcf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7e)) s (0x105fcf + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105fcf 5 0 (.sib 4 none 0 (.d8 0x7e)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105fcf 5 0 (.sib 4 none 0 (.d8 0x7e))).toInstrSpec (movzx_r32_m16_effect_step 0x105fcf 0 (.sib 4 none 0 (.d8 0x7e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f543 : InstrSpec 0x105fd4 [0x89, 0xC1] (fun s => s.RIP = 0x105fd4) (movR32R32Effect 0x105fd4 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105fd4 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105fd4 0xc1 (by decide)) pre_rip
  have f544 : InstrSpec 0x105fd6 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105fd6) (shrR32Effect 0x105fd6 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105fd6 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105fd6 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f545 : InstrSpec 0x105fd9 [0x31, 0xC1] (fun s => s.RIP = 0x105fd9) (xorR32R32Effect 0x105fd9 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105fd9 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105fd9 0xc1 (by decide)) pre_rip
  have f546 : InstrSpec 0x105fdb [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x105fdb) (andR32Imm32Effect 0x105fdb 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105fdb 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x105fdb 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f547 : InstrSpec 0x105fe1 [0x31, 0xC8] (fun s => s.RIP = 0x105fe1) (xorR32R32Effect 0x105fe1 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105fe1 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105fe1 0xc8 (by decide)) pre_rip
  have f548 : InstrSpec 0x105fe3 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105fe3) (shlR32Effect 0x105fe3 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105fe3 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105fe3 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f549 : InstrSpec 0x105fe6 [0x31, 0xC1] (fun s => s.RIP = 0x105fe6) (xorR32R32Effect 0x105fe6 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105fe6 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105fe6 0xc1 (by decide)) pre_rip
  have f550 : InstrSpec 0x105fe8 [0x89, 0xC8] (fun s => s.RIP = 0x105fe8) (movR32R32Effect 0x105fe8 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105fe8 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105fe8 0xc8 (by decide)) pre_rip
  have f551 : InstrSpec 0x105fea [0xD1, 0xE8] (fun s => s.RIP = 0x105fea) (shrR32Effect 0x105fea 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105fea 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105fea 0xe8 (by decide) (by decide)) pre_rip
  have f552 : InstrSpec 0x105fec [0x31, 0xC8] (fun s => s.RIP = 0x105fec) (xorR32R32Effect 0x105fec 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105fec 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105fec 0xc8 (by decide)) pre_rip
  have f553 : InstrSpec 0x105fee [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105fee) (andEaxImm32Effect 0x105fee 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105fee 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105fee 0x5050) pre_rip
  have f554 : InstrSpec 0x105ff3 [0x31, 0xC1] (fun s => s.RIP = 0x105ff3) (xorR32R32Effect 0x105ff3 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105ff3 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105ff3 0xc1 (by decide)) pre_rip
  have f555 : InstrSpec 0x105ff5 [0x01, 0xC0] (fun s => s.RIP = 0x105ff5) (addR32R32Effect 0x105ff5 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105ff5 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105ff5 0xc0 (by decide)) pre_rip
  have f556 : InstrSpec 0x105ff7 [0x31, 0xC8] (fun s => s.RIP = 0x105ff7) (xorR32R32Effect 0x105ff7 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105ff7 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105ff7 0xc8 (by decide)) pre_rip
  have f557 : InstrSpec 0x105ff9 [0x66, 0x89, 0x44, 0x24, 0x7E] (StorePre 0x105ff9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7e)) s (0x105ff9 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105ff9 5 0 (.sib 4 none 0 (.d8 0x7e)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105ff9 5 0 (.sib 4 none 0 (.d8 0x7e))).toInstrSpec (mov_m16_r16_effect_step 0x105ff9 0 (.sib 4 none 0 (.d8 0x7e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f558 : InstrSpec 0x105ffe [0x0F, 0xB7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x105ffe (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x105ffe + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x105ffe 8 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105ffe 8 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (movzx_r32_m16_effect_step 0x105ffe 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f559 : InstrSpec 0x106006 [0x89, 0xC1] (fun s => s.RIP = 0x106006) (movR32R32Effect 0x106006 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106006 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x106006 0xc1 (by decide)) pre_rip
  refine Rest.ofInside (n := 1094) (RestInside.out (n := 1094) f540 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1095) (ρ' := [(0, 1078), (1, 1092), (4, 4), (9, 1033), (14, 1049), (15, 1094), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fcc) f540 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1096) (RestInside.out (n := 1096) f541 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1097) (ρ' := [(0, 1078), (1, 1092), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fcf) f541 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1098) (RestInside.out (n := 1098) f542 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1099) (ρ' := [(0, 1098), (1, 1092), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fd4) f542 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1100) (RestInside.out (n := 1100) f543 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1101) (ρ' := [(0, 1098), (1, 1100), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fd6) f543 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1102) (RestInside.out (n := 1102) f544 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1103) (ρ' := [(0, 1098), (1, 1102), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fd9) f544 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1104) (RestInside.out (n := 1104) f545 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1105) (ρ' := [(0, 1098), (1, 1104), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fdb) f545 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1106) (RestInside.out (n := 1106) f546 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1107) (ρ' := [(0, 1098), (1, 1106), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fe1) f546 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1108) (RestInside.out (n := 1108) f547 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1109) (ρ' := [(0, 1108), (1, 1106), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fe3) f547 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1110) (RestInside.out (n := 1110) f548 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1111) (ρ' := [(0, 1108), (1, 1110), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fe6) f548 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1112) (RestInside.out (n := 1112) f549 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1113) (ρ' := [(0, 1108), (1, 1112), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fe8) f549 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1114) (RestInside.out (n := 1114) f550 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1115) (ρ' := [(0, 1114), (1, 1112), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fea) f550 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1116) (RestInside.out (n := 1116) f551 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1117) (ρ' := [(0, 1116), (1, 1112), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fec) f551 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1118) (RestInside.out (n := 1118) f552 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1119) (ρ' := [(0, 1118), (1, 1112), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fee) f552 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1120) (RestInside.out (n := 1120) f553 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1121) (ρ' := [(0, 1120), (1, 1112), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ff3) f553 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1122) (RestInside.out (n := 1122) f554 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1123) (ρ' := [(0, 1120), (1, 1122), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ff5) f554 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1124) (RestInside.out (n := 1124) f555 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1125) (ρ' := [(0, 1124), (1, 1122), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ff7) f555 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1126) (RestInside.out (n := 1126) f556 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1127) (ρ' := [(0, 1126), (1, 1122), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ff9) f556 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1128) (RestInside.exec (n := 1128) (ρ' := [(0, 1126), (1, 1122), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ffe) f557 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1129) (RestInside.out (n := 1129) f558 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1130) (ρ' := [(0, 1129), (1, 1122), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106006) f558 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1131) (RestInside.out (n := 1131) f559 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1132) (ρ' := [(0, 1129), (1, 1131), (4, 4), (9, 1033), (14, 1049), (15, 1096), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106008) f559 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_28 code

theorem rest_l10593a_26 [Bindings] (code : CodeMap) :
    Rest (n := 1055) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1051), (1, 1053), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]
      672 0x105f86 bytes_l10593a_26 b_l10593a_26 := by
  have f520 : InstrSpec 0x105f86 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105f86) (shrR32Effect 0x105f86 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105f86 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105f86 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f521 : InstrSpec 0x105f89 [0x31, 0xC1] (fun s => s.RIP = 0x105f89) (xorR32R32Effect 0x105f89 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105f89 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105f89 0xc1 (by decide)) pre_rip
  have f522 : InstrSpec 0x105f8b [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105f8b) (andR32Imm32Effect 0x105f8b 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105f8b 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x105f8b 0xe1 0x3030 (by decide) (by decide)) pre_rip
  have f523 : InstrSpec 0x105f91 [0x31, 0xC8] (fun s => s.RIP = 0x105f91) (xorR32R32Effect 0x105f91 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105f91 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105f91 0xc8 (by decide)) pre_rip
  have f524 : InstrSpec 0x105f93 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105f93) (shlR32Effect 0x105f93 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105f93 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105f93 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f525 : InstrSpec 0x105f96 [0x31, 0xC1] (fun s => s.RIP = 0x105f96) (xorR32R32Effect 0x105f96 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105f96 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105f96 0xc1 (by decide)) pre_rip
  have f526 : InstrSpec 0x105f98 [0x66, 0x89, 0x4C, 0x24, 0x7A] (StorePre 0x105f98 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7a)) s (0x105f98 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105f98 5 1 (.sib 4 none 0 (.d8 0x7a)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105f98 5 1 (.sib 4 none 0 (.d8 0x7a))).toInstrSpec (mov_m16_r16_effect_step 0x105f98 1 (.sib 4 none 0 (.d8 0x7a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f527 : InstrSpec 0x105f9d [0x0F, 0xB7, 0x44, 0x24, 0x7C] (LoadPre 0x105f9d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x105f9d + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105f9d 5 0 (.sib 4 none 0 (.d8 0x7c)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105f9d 5 0 (.sib 4 none 0 (.d8 0x7c))).toInstrSpec (movzx_r32_m16_effect_step 0x105f9d 0 (.sib 4 none 0 (.d8 0x7c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f528 : InstrSpec 0x105fa2 [0x89, 0xC1] (fun s => s.RIP = 0x105fa2) (movR32R32Effect 0x105fa2 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105fa2 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105fa2 0xc1 (by decide)) pre_rip
  have f529 : InstrSpec 0x105fa4 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105fa4) (shrR32Effect 0x105fa4 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105fa4 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105fa4 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f530 : InstrSpec 0x105fa7 [0x31, 0xC1] (fun s => s.RIP = 0x105fa7) (xorR32R32Effect 0x105fa7 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105fa7 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105fa7 0xc1 (by decide)) pre_rip
  have f531 : InstrSpec 0x105fa9 [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x105fa9) (andR32Imm32Effect 0x105fa9 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105fa9 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x105fa9 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f532 : InstrSpec 0x105faf [0x31, 0xC8] (fun s => s.RIP = 0x105faf) (xorR32R32Effect 0x105faf 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105faf 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105faf 0xc8 (by decide)) pre_rip
  have f533 : InstrSpec 0x105fb1 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105fb1) (shlR32Effect 0x105fb1 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105fb1 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105fb1 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f534 : InstrSpec 0x105fb4 [0x31, 0xC1] (fun s => s.RIP = 0x105fb4) (xorR32R32Effect 0x105fb4 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105fb4 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105fb4 0xc1 (by decide)) pre_rip
  have f535 : InstrSpec 0x105fb6 [0x41, 0x89, 0xCF] (fun s => s.RIP = 0x105fb6) (movR32R32Effect 0x105fb6 3 15 1)
      [.gpr 1] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x105fb6 3 15 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x105fb6 0x41 0xcf (by decide) (by decide)) pre_rip
  have f536 : InstrSpec 0x105fb9 [0x41, 0xD1, 0xEF] (fun s => s.RIP = 0x105fb9) (shrR32Effect 0x105fb9 3 15 1)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR32Effect_footprint 0x105fb9 3 15 1).toInstrSpec (shr_r32_one_rex_effect_step 0x105fb9 0x41 0xef (by decide) (by decide) (by decide)) pre_rip
  have f537 : InstrSpec 0x105fbc [0x41, 0x31, 0xCF] (fun s => s.RIP = 0x105fbc) (xorR32R32Effect 0x105fbc 3 15 1)
      [.gpr 15, .gpr 1] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105fbc 3 15 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x105fbc 0x41 0xcf (by decide) (by decide)) pre_rip
  have f538 : InstrSpec 0x105fbf [0x41, 0x81, 0xE7, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105fbf) (andR32Imm32Effect 0x105fbf 7 15 0x5050)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105fbf 7 15 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x105fbf 0x41 0xe7 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f539 : InstrSpec 0x105fc6 [0x44, 0x31, 0xF9] (fun s => s.RIP = 0x105fc6) (xorR32R32Effect 0x105fc6 3 1 15)
      [.gpr 1, .gpr 15] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105fc6 3 1 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x105fc6 0x44 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1055) (RestInside.out (n := 1055) f520 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1056) (ρ' := [(0, 1051), (1, 1055), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f89) f520 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1057) (RestInside.out (n := 1057) f521 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1058) (ρ' := [(0, 1051), (1, 1057), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f8b) f521 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1059) (RestInside.out (n := 1059) f522 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1060) (ρ' := [(0, 1051), (1, 1059), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f91) f522 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1061) (RestInside.out (n := 1061) f523 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1062) (ρ' := [(0, 1061), (1, 1059), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f93) f523 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1063) (RestInside.out (n := 1063) f524 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1064) (ρ' := [(0, 1061), (1, 1063), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f96) f524 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1065) (RestInside.out (n := 1065) f525 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1066) (ρ' := [(0, 1061), (1, 1065), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f98) f525 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1067) (RestInside.exec (n := 1067) (ρ' := [(0, 1061), (1, 1065), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f9d) f526 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1068) (RestInside.out (n := 1068) f527 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1069) (ρ' := [(0, 1068), (1, 1065), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fa2) f527 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1070) (RestInside.out (n := 1070) f528 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1071) (ρ' := [(0, 1068), (1, 1070), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fa4) f528 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1072) (RestInside.out (n := 1072) f529 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1073) (ρ' := [(0, 1068), (1, 1072), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fa7) f529 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1074) (RestInside.out (n := 1074) f530 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1075) (ρ' := [(0, 1068), (1, 1074), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fa9) f530 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1076) (RestInside.out (n := 1076) f531 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1077) (ρ' := [(0, 1068), (1, 1076), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105faf) f531 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1078) (RestInside.out (n := 1078) f532 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1079) (ρ' := [(0, 1078), (1, 1076), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fb1) f532 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1080) (RestInside.out (n := 1080) f533 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1081) (ρ' := [(0, 1078), (1, 1080), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fb4) f533 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1082) (RestInside.out (n := 1082) f534 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1083) (ρ' := [(0, 1078), (1, 1082), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fb6) f534 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1084) (RestInside.out (n := 1084) f535 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1085) (ρ' := [(0, 1078), (1, 1082), (4, 4), (9, 1033), (14, 1049), (15, 1084), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fb9) f535 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1086) (RestInside.out (n := 1086) f536 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1087) (ρ' := [(0, 1078), (1, 1082), (4, 4), (9, 1033), (14, 1049), (15, 1086), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fbc) f536 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1088) (RestInside.out (n := 1088) f537 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1089) (ρ' := [(0, 1078), (1, 1082), (4, 4), (9, 1033), (14, 1049), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fbf) f537 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1090) (RestInside.out (n := 1090) f538 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1091) (ρ' := [(0, 1078), (1, 1082), (4, 4), (9, 1033), (14, 1049), (15, 1090), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fc6) f538 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1092) (RestInside.out (n := 1092) f539 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1093) (ρ' := [(0, 1078), (1, 1092), (4, 4), (9, 1033), (14, 1049), (15, 1090), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fc9) f539 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_27 code

theorem rest_l10593a_25 [Bindings] (code : CodeMap) :
    Rest (n := 1016) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 1012), (1, 1014), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      692 0x105f38 bytes_l10593a_25 b_l10593a_25 := by
  have f500 : InstrSpec 0x105f38 [0x31, 0xC1] (fun s => s.RIP = 0x105f38) (xorR32R32Effect 0x105f38 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105f38 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105f38 0xc1 (by decide)) pre_rip
  have f501 : InstrSpec 0x105f3a [0x66, 0x89, 0x4C, 0x24, 0x74] (StorePre 0x105f3a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x105f3a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105f3a 5 1 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105f3a 5 1 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (mov_m16_r16_effect_step 0x105f3a 1 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f502 : InstrSpec 0x105f3f [0x0F, 0xB7, 0x44, 0x24, 0x76] (LoadPre 0x105f3f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x105f3f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105f3f 5 0 (.sib 4 none 0 (.d8 0x76)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105f3f 5 0 (.sib 4 none 0 (.d8 0x76))).toInstrSpec (movzx_r32_m16_effect_step 0x105f3f 0 (.sib 4 none 0 (.d8 0x76)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f503 : InstrSpec 0x105f44 [0x41, 0x89, 0xC1] (fun s => s.RIP = 0x105f44) (movR32R32Effect 0x105f44 3 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x105f44 3 9 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x105f44 0x41 0xc1 (by decide) (by decide)) pre_rip
  have f504 : InstrSpec 0x105f47 [0x41, 0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105f47) (shrR32Effect 0x105f47 4 9 2)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x105f47 4 9 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x105f47 0x41 0xe9 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f505 : InstrSpec 0x105f4b [0x41, 0x31, 0xC1] (fun s => s.RIP = 0x105f4b) (xorR32R32Effect 0x105f4b 3 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105f4b 3 9 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x105f4b 0x41 0xc1 (by decide) (by decide)) pre_rip
  have f506 : InstrSpec 0x105f4e [0x41, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105f4e) (andR32Imm32Effect 0x105f4e 7 9 0x3030)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105f4e 7 9 0x3030).toInstrSpec (and_r32_imm32_rex_effect_step 0x105f4e 0x41 0xe1 0x3030 (by decide) (by decide) (by decide)) pre_rip
  have f507 : InstrSpec 0x105f55 [0x44, 0x31, 0xC8] (fun s => s.RIP = 0x105f55) (xorR32R32Effect 0x105f55 3 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105f55 3 0 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x105f55 0x44 0xc8 (by decide) (by decide)) pre_rip
  have f508 : InstrSpec 0x105f58 [0x41, 0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105f58) (shlR32Effect 0x105f58 4 9 2)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR32Effect_footprint 0x105f58 4 9 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x105f58 0x41 0xe1 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f509 : InstrSpec 0x105f5c [0x41, 0x31, 0xC1] (fun s => s.RIP = 0x105f5c) (xorR32R32Effect 0x105f5c 3 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105f5c 3 9 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x105f5c 0x41 0xc1 (by decide) (by decide)) pre_rip
  have f510 : InstrSpec 0x105f5f [0x0F, 0xB7, 0x44, 0x24, 0x78] (LoadPre 0x105f5f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x105f5f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105f5f 5 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105f5f 5 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (movzx_r32_m16_effect_step 0x105f5f 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f511 : InstrSpec 0x105f64 [0x41, 0x89, 0xC6] (fun s => s.RIP = 0x105f64) (movR32R32Effect 0x105f64 3 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x105f64 3 14 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x105f64 0x41 0xc6 (by decide) (by decide)) pre_rip
  have f512 : InstrSpec 0x105f67 [0x41, 0xC1, 0xEE, 0x02] (fun s => s.RIP = 0x105f67) (shrR32Effect 0x105f67 4 14 2)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR32Effect_footprint 0x105f67 4 14 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x105f67 0x41 0xee 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f513 : InstrSpec 0x105f6b [0x41, 0x31, 0xC6] (fun s => s.RIP = 0x105f6b) (xorR32R32Effect 0x105f6b 3 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105f6b 3 14 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x105f6b 0x41 0xc6 (by decide) (by decide)) pre_rip
  have f514 : InstrSpec 0x105f6e [0x41, 0x81, 0xE6, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105f6e) (andR32Imm32Effect 0x105f6e 7 14 0x3030)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105f6e 7 14 0x3030).toInstrSpec (and_r32_imm32_rex_effect_step 0x105f6e 0x41 0xe6 0x3030 (by decide) (by decide) (by decide)) pre_rip
  have f515 : InstrSpec 0x105f75 [0x44, 0x31, 0xF0] (fun s => s.RIP = 0x105f75) (xorR32R32Effect 0x105f75 3 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105f75 3 0 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x105f75 0x44 0xf0 (by decide) (by decide)) pre_rip
  have f516 : InstrSpec 0x105f78 [0x41, 0xC1, 0xE6, 0x02] (fun s => s.RIP = 0x105f78) (shlR32Effect 0x105f78 4 14 2)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shlR32Effect_footprint 0x105f78 4 14 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x105f78 0x41 0xe6 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f517 : InstrSpec 0x105f7c [0x41, 0x31, 0xC6] (fun s => s.RIP = 0x105f7c) (xorR32R32Effect 0x105f7c 3 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105f7c 3 14 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x105f7c 0x41 0xc6 (by decide) (by decide)) pre_rip
  have f518 : InstrSpec 0x105f7f [0x0F, 0xB7, 0x44, 0x24, 0x7A] (LoadPre 0x105f7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7a)) s (0x105f7f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105f7f 5 0 (.sib 4 none 0 (.d8 0x7a)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105f7f 5 0 (.sib 4 none 0 (.d8 0x7a))).toInstrSpec (movzx_r32_m16_effect_step 0x105f7f 0 (.sib 4 none 0 (.d8 0x7a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f519 : InstrSpec 0x105f84 [0x89, 0xC1] (fun s => s.RIP = 0x105f84) (movR32R32Effect 0x105f84 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105f84 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105f84 0xc1 (by decide)) pre_rip
  refine Rest.ofInside (n := 1016) (RestInside.out (n := 1016) f500 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1017) (ρ' := [(0, 1012), (1, 1016), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f3a) f500 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1018) (RestInside.exec (n := 1018) (ρ' := [(0, 1012), (1, 1016), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f3f) f501 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1019) (RestInside.out (n := 1019) f502 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1020) (ρ' := [(0, 1019), (1, 1016), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f44) f502 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1021) (RestInside.out (n := 1021) f503 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1022) (ρ' := [(0, 1019), (1, 1016), (4, 4), (9, 1021), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f47) f503 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1023) (RestInside.out (n := 1023) f504 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1024) (ρ' := [(0, 1019), (1, 1016), (4, 4), (9, 1023), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f4b) f504 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1025) (RestInside.out (n := 1025) f505 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1026) (ρ' := [(0, 1019), (1, 1016), (4, 4), (9, 1025), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f4e) f505 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1027) (RestInside.out (n := 1027) f506 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1028) (ρ' := [(0, 1019), (1, 1016), (4, 4), (9, 1027), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f55) f506 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1029) (RestInside.out (n := 1029) f507 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1030) (ρ' := [(0, 1029), (1, 1016), (4, 4), (9, 1027), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f58) f507 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1031) (RestInside.out (n := 1031) f508 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1032) (ρ' := [(0, 1029), (1, 1016), (4, 4), (9, 1031), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f5c) f508 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1033) (RestInside.out (n := 1033) f509 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1034) (ρ' := [(0, 1029), (1, 1016), (4, 4), (9, 1033), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f5f) f509 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1035) (RestInside.out (n := 1035) f510 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1036) (ρ' := [(0, 1035), (1, 1016), (4, 4), (9, 1033), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f64) f510 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1037) (RestInside.out (n := 1037) f511 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1038) (ρ' := [(0, 1035), (1, 1016), (4, 4), (9, 1033), (14, 1037), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f67) f511 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1039) (RestInside.out (n := 1039) f512 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1040) (ρ' := [(0, 1035), (1, 1016), (4, 4), (9, 1033), (14, 1039), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f6b) f512 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1041) (RestInside.out (n := 1041) f513 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1042) (ρ' := [(0, 1035), (1, 1016), (4, 4), (9, 1033), (14, 1041), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f6e) f513 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1043) (RestInside.out (n := 1043) f514 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1044) (ρ' := [(0, 1035), (1, 1016), (4, 4), (9, 1033), (14, 1043), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f75) f514 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1045) (RestInside.out (n := 1045) f515 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1046) (ρ' := [(0, 1045), (1, 1016), (4, 4), (9, 1033), (14, 1043), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f78) f515 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1047) (RestInside.out (n := 1047) f516 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1048) (ρ' := [(0, 1045), (1, 1016), (4, 4), (9, 1033), (14, 1047), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f7c) f516 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1049) (RestInside.out (n := 1049) f517 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1050) (ρ' := [(0, 1045), (1, 1016), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f7f) f517 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1051) (RestInside.out (n := 1051) f518 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1052) (ρ' := [(0, 1051), (1, 1016), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f84) f518 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1053) (RestInside.out (n := 1053) f519 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1054) (ρ' := [(0, 1051), (1, 1053), (4, 4), (9, 1033), (14, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f86) f519 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_26 code

theorem rest_l10593a_24 [Bindings] (code : CodeMap) :
    Rest (n := 978) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 968), (1, 976), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      712 0x105ef7 bytes_l10593a_24 b_l10593a_24 := by
  have f480 : InstrSpec 0x105ef7 [0x31, 0xC8] (fun s => s.RIP = 0x105ef7) (xorR32R32Effect 0x105ef7 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105ef7 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105ef7 0xc8 (by decide)) pre_rip
  have f481 : InstrSpec 0x105ef9 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105ef9) (shlR32Effect 0x105ef9 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105ef9 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105ef9 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f482 : InstrSpec 0x105efc [0x31, 0xC1] (fun s => s.RIP = 0x105efc) (xorR32R32Effect 0x105efc 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105efc 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105efc 0xc1 (by decide)) pre_rip
  have f483 : InstrSpec 0x105efe [0x66, 0x89, 0x4C, 0x24, 0x70] (StorePre 0x105efe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x105efe + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105efe 5 1 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105efe 5 1 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m16_r16_effect_step 0x105efe 1 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f484 : InstrSpec 0x105f03 [0x0F, 0xB7, 0x44, 0x24, 0x72] (LoadPre 0x105f03 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x105f03 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105f03 5 0 (.sib 4 none 0 (.d8 0x72)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105f03 5 0 (.sib 4 none 0 (.d8 0x72))).toInstrSpec (movzx_r32_m16_effect_step 0x105f03 0 (.sib 4 none 0 (.d8 0x72)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f485 : InstrSpec 0x105f08 [0x89, 0xC1] (fun s => s.RIP = 0x105f08) (movR32R32Effect 0x105f08 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105f08 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105f08 0xc1 (by decide)) pre_rip
  have f486 : InstrSpec 0x105f0a [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105f0a) (shrR32Effect 0x105f0a 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105f0a 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105f0a 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f487 : InstrSpec 0x105f0d [0x31, 0xC1] (fun s => s.RIP = 0x105f0d) (xorR32R32Effect 0x105f0d 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105f0d 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105f0d 0xc1 (by decide)) pre_rip
  have f488 : InstrSpec 0x105f0f [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105f0f) (andR32Imm32Effect 0x105f0f 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105f0f 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x105f0f 0xe1 0x3030 (by decide) (by decide)) pre_rip
  have f489 : InstrSpec 0x105f15 [0x31, 0xC8] (fun s => s.RIP = 0x105f15) (xorR32R32Effect 0x105f15 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105f15 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105f15 0xc8 (by decide)) pre_rip
  have f490 : InstrSpec 0x105f17 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105f17) (shlR32Effect 0x105f17 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105f17 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105f17 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f491 : InstrSpec 0x105f1a [0x31, 0xC1] (fun s => s.RIP = 0x105f1a) (xorR32R32Effect 0x105f1a 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105f1a 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105f1a 0xc1 (by decide)) pre_rip
  have f492 : InstrSpec 0x105f1c [0x66, 0x89, 0x4C, 0x24, 0x72] (StorePre 0x105f1c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x105f1c + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105f1c 5 1 (.sib 4 none 0 (.d8 0x72)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105f1c 5 1 (.sib 4 none 0 (.d8 0x72))).toInstrSpec (mov_m16_r16_effect_step 0x105f1c 1 (.sib 4 none 0 (.d8 0x72)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f493 : InstrSpec 0x105f21 [0x0F, 0xB7, 0x44, 0x24, 0x74] (LoadPre 0x105f21 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x105f21 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105f21 5 0 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105f21 5 0 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (movzx_r32_m16_effect_step 0x105f21 0 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f494 : InstrSpec 0x105f26 [0x89, 0xC1] (fun s => s.RIP = 0x105f26) (movR32R32Effect 0x105f26 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105f26 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105f26 0xc1 (by decide)) pre_rip
  have f495 : InstrSpec 0x105f28 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105f28) (shrR32Effect 0x105f28 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105f28 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105f28 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f496 : InstrSpec 0x105f2b [0x31, 0xC1] (fun s => s.RIP = 0x105f2b) (xorR32R32Effect 0x105f2b 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105f2b 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105f2b 0xc1 (by decide)) pre_rip
  have f497 : InstrSpec 0x105f2d [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105f2d) (andR32Imm32Effect 0x105f2d 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105f2d 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x105f2d 0xe1 0x3030 (by decide) (by decide)) pre_rip
  have f498 : InstrSpec 0x105f33 [0x31, 0xC8] (fun s => s.RIP = 0x105f33) (xorR32R32Effect 0x105f33 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105f33 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105f33 0xc8 (by decide)) pre_rip
  have f499 : InstrSpec 0x105f35 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105f35) (shlR32Effect 0x105f35 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105f35 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105f35 0xe1 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 978) (RestInside.out (n := 978) f480 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 979) (ρ' := [(0, 978), (1, 976), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ef9) f480 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 980) (RestInside.out (n := 980) f481 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 981) (ρ' := [(0, 978), (1, 980), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105efc) f481 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 982) (RestInside.out (n := 982) f482 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 983) (ρ' := [(0, 978), (1, 982), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105efe) f482 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 984) (RestInside.exec (n := 984) (ρ' := [(0, 978), (1, 982), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f03) f483 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 985) (RestInside.out (n := 985) f484 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 986) (ρ' := [(0, 985), (1, 982), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f08) f484 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 987) (RestInside.out (n := 987) f485 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 988) (ρ' := [(0, 985), (1, 987), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f0a) f485 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 989) (RestInside.out (n := 989) f486 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 990) (ρ' := [(0, 985), (1, 989), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f0d) f486 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 991) (RestInside.out (n := 991) f487 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 992) (ρ' := [(0, 985), (1, 991), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f0f) f487 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 993) (RestInside.out (n := 993) f488 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 994) (ρ' := [(0, 985), (1, 993), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f15) f488 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 995) (RestInside.out (n := 995) f489 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 996) (ρ' := [(0, 995), (1, 993), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f17) f489 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 997) (RestInside.out (n := 997) f490 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 998) (ρ' := [(0, 995), (1, 997), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f1a) f490 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 999) (RestInside.out (n := 999) f491 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1000) (ρ' := [(0, 995), (1, 999), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f1c) f491 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1001) (RestInside.exec (n := 1001) (ρ' := [(0, 995), (1, 999), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f21) f492 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1002) (RestInside.out (n := 1002) f493 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1003) (ρ' := [(0, 1002), (1, 999), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f26) f493 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1004) (RestInside.out (n := 1004) f494 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1005) (ρ' := [(0, 1002), (1, 1004), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f28) f494 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1006) (RestInside.out (n := 1006) f495 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1007) (ρ' := [(0, 1002), (1, 1006), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f2b) f495 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1008) (RestInside.out (n := 1008) f496 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1009) (ρ' := [(0, 1002), (1, 1008), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f2d) f496 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1010) (RestInside.out (n := 1010) f497 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1011) (ρ' := [(0, 1002), (1, 1010), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f33) f497 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1012) (RestInside.out (n := 1012) f498 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1013) (ρ' := [(0, 1012), (1, 1010), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f35) f498 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1014) (RestInside.out (n := 1014) f499 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1015) (ρ' := [(0, 1012), (1, 1014), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f38) f499 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_25 code

theorem rest_l10593a_23 [Bindings] (code : CodeMap) :
    Rest (n := 940) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 934), (1, 938), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      732 0x105eaf bytes_l10593a_23 b_l10593a_23 := by
  have f460 : InstrSpec 0x105eaf [0x31, 0xC1] (fun s => s.RIP = 0x105eaf) (xorR32R32Effect 0x105eaf 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105eaf 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105eaf 0xc1 (by decide)) pre_rip
  have f461 : InstrSpec 0x105eb1 [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105eb1) (andR32Imm32Effect 0x105eb1 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105eb1 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x105eb1 0xe1 0x3030 (by decide) (by decide)) pre_rip
  have f462 : InstrSpec 0x105eb7 [0x31, 0xC8] (fun s => s.RIP = 0x105eb7) (xorR32R32Effect 0x105eb7 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105eb7 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105eb7 0xc8 (by decide)) pre_rip
  have f463 : InstrSpec 0x105eb9 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105eb9) (shlR32Effect 0x105eb9 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105eb9 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105eb9 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f464 : InstrSpec 0x105ebc [0x31, 0xC1] (fun s => s.RIP = 0x105ebc) (xorR32R32Effect 0x105ebc 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105ebc 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105ebc 0xc1 (by decide)) pre_rip
  have f465 : InstrSpec 0x105ebe [0x89, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x105ebe 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x105ebe + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105ebe 1 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x105ebe 1 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m32_r32_low_effect_step 0x105ebe 1 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f466 : InstrSpec 0x105ec5 [0x0F, 0xB7, 0x44, 0x24, 0x6E] (LoadPre 0x105ec5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6e)) s (0x105ec5 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105ec5 5 0 (.sib 4 none 0 (.d8 0x6e)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105ec5 5 0 (.sib 4 none 0 (.d8 0x6e))).toInstrSpec (movzx_r32_m16_effect_step 0x105ec5 0 (.sib 4 none 0 (.d8 0x6e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f467 : InstrSpec 0x105eca [0x89, 0xC1] (fun s => s.RIP = 0x105eca) (movR32R32Effect 0x105eca 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105eca 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105eca 0xc1 (by decide)) pre_rip
  have f468 : InstrSpec 0x105ecc [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105ecc) (shrR32Effect 0x105ecc 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105ecc 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105ecc 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f469 : InstrSpec 0x105ecf [0x31, 0xC1] (fun s => s.RIP = 0x105ecf) (xorR32R32Effect 0x105ecf 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105ecf 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105ecf 0xc1 (by decide)) pre_rip
  have f470 : InstrSpec 0x105ed1 [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105ed1) (andR32Imm32Effect 0x105ed1 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105ed1 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x105ed1 0xe1 0x3030 (by decide) (by decide)) pre_rip
  have f471 : InstrSpec 0x105ed7 [0x31, 0xC8] (fun s => s.RIP = 0x105ed7) (xorR32R32Effect 0x105ed7 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105ed7 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105ed7 0xc8 (by decide)) pre_rip
  have f472 : InstrSpec 0x105ed9 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105ed9) (shlR32Effect 0x105ed9 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105ed9 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105ed9 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f473 : InstrSpec 0x105edc [0x31, 0xC1] (fun s => s.RIP = 0x105edc) (xorR32R32Effect 0x105edc 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105edc 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105edc 0xc1 (by decide)) pre_rip
  have f474 : InstrSpec 0x105ede [0x89, 0x8C, 0x24, 0xFC, 0x00, 0x00, 0x00] (StorePre 0x105ede 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xfc)) s (0x105ede + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105ede 1 (.sib 4 none 0 (.d32 0xfc)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x105ede 1 (.sib 4 none 0 (.d32 0xfc))).toInstrSpec (mov_m32_r32_low_effect_step 0x105ede 1 (.sib 4 none 0 (.d32 0xfc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f475 : InstrSpec 0x105ee5 [0x0F, 0xB7, 0x44, 0x24, 0x70] (LoadPre 0x105ee5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x105ee5 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105ee5 5 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105ee5 5 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (movzx_r32_m16_effect_step 0x105ee5 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f476 : InstrSpec 0x105eea [0x89, 0xC1] (fun s => s.RIP = 0x105eea) (movR32R32Effect 0x105eea 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105eea 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105eea 0xc1 (by decide)) pre_rip
  have f477 : InstrSpec 0x105eec [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105eec) (shrR32Effect 0x105eec 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105eec 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105eec 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f478 : InstrSpec 0x105eef [0x31, 0xC1] (fun s => s.RIP = 0x105eef) (xorR32R32Effect 0x105eef 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105eef 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105eef 0xc1 (by decide)) pre_rip
  have f479 : InstrSpec 0x105ef1 [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105ef1) (andR32Imm32Effect 0x105ef1 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105ef1 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x105ef1 0xe1 0x3030 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 940) (RestInside.out (n := 940) f460 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 941) (ρ' := [(0, 934), (1, 940), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105eb1) f460 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 942) (RestInside.out (n := 942) f461 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 943) (ρ' := [(0, 934), (1, 942), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105eb7) f461 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 944) (RestInside.out (n := 944) f462 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 945) (ρ' := [(0, 944), (1, 942), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105eb9) f462 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 946) (RestInside.out (n := 946) f463 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 947) (ρ' := [(0, 944), (1, 946), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ebc) f463 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 948) (RestInside.out (n := 948) f464 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 949) (ρ' := [(0, 944), (1, 948), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ebe) f464 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 950) (RestInside.exec (n := 950) (ρ' := [(0, 944), (1, 948), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ec5) f465 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 951) (RestInside.out (n := 951) f466 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 952) (ρ' := [(0, 951), (1, 948), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105eca) f466 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 953) (RestInside.out (n := 953) f467 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 954) (ρ' := [(0, 951), (1, 953), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ecc) f467 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 955) (RestInside.out (n := 955) f468 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 956) (ρ' := [(0, 951), (1, 955), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ecf) f468 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 957) (RestInside.out (n := 957) f469 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 958) (ρ' := [(0, 951), (1, 957), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ed1) f469 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 959) (RestInside.out (n := 959) f470 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 960) (ρ' := [(0, 951), (1, 959), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ed7) f470 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 961) (RestInside.out (n := 961) f471 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 962) (ρ' := [(0, 961), (1, 959), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ed9) f471 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 963) (RestInside.out (n := 963) f472 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 964) (ρ' := [(0, 961), (1, 963), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105edc) f472 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 965) (RestInside.out (n := 965) f473 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 966) (ρ' := [(0, 961), (1, 965), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ede) f473 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 967) (RestInside.exec (n := 967) (ρ' := [(0, 961), (1, 965), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ee5) f474 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 968) (RestInside.out (n := 968) f475 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 969) (ρ' := [(0, 968), (1, 965), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105eea) f475 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 970) (RestInside.out (n := 970) f476 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 971) (ρ' := [(0, 968), (1, 970), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105eec) f476 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 972) (RestInside.out (n := 972) f477 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 973) (ρ' := [(0, 968), (1, 972), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105eef) f477 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 974) (RestInside.out (n := 974) f478 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 975) (ρ' := [(0, 968), (1, 974), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ef1) f478 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 976) (RestInside.out (n := 976) f479 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 977) (ρ' := [(0, 968), (1, 976), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ef7) f479 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_24 code

theorem rest_l10593a_22 [Bindings] (code : CodeMap) :
    Rest (n := 902) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 900), (1, 896), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      752 0x105e71 bytes_l10593a_22 b_l10593a_22 := by
  have f440 : InstrSpec 0x105e71 [0x66, 0x89, 0x44, 0x24, 0x68] (StorePre 0x105e71 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x105e71 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105e71 5 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105e71 5 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m16_r16_effect_step 0x105e71 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f441 : InstrSpec 0x105e76 [0x0F, 0xB7, 0x44, 0x24, 0x6A] (LoadPre 0x105e76 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6a)) s (0x105e76 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105e76 5 0 (.sib 4 none 0 (.d8 0x6a)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105e76 5 0 (.sib 4 none 0 (.d8 0x6a))).toInstrSpec (movzx_r32_m16_effect_step 0x105e76 0 (.sib 4 none 0 (.d8 0x6a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f442 : InstrSpec 0x105e7b [0x89, 0xC1] (fun s => s.RIP = 0x105e7b) (movR32R32Effect 0x105e7b 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105e7b 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105e7b 0xc1 (by decide)) pre_rip
  have f443 : InstrSpec 0x105e7d [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105e7d) (shrR32Effect 0x105e7d 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105e7d 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105e7d 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f444 : InstrSpec 0x105e80 [0x31, 0xC1] (fun s => s.RIP = 0x105e80) (xorR32R32Effect 0x105e80 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e80 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105e80 0xc1 (by decide)) pre_rip
  have f445 : InstrSpec 0x105e82 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x105e82) (andR32Imm32Effect 0x105e82 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105e82 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x105e82 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f446 : InstrSpec 0x105e88 [0x31, 0xC8] (fun s => s.RIP = 0x105e88) (xorR32R32Effect 0x105e88 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e88 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105e88 0xc8 (by decide)) pre_rip
  have f447 : InstrSpec 0x105e8a [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105e8a) (shlR32Effect 0x105e8a 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105e8a 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105e8a 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f448 : InstrSpec 0x105e8d [0x31, 0xC1] (fun s => s.RIP = 0x105e8d) (xorR32R32Effect 0x105e8d 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e8d 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105e8d 0xc1 (by decide)) pre_rip
  have f449 : InstrSpec 0x105e8f [0x89, 0xC8] (fun s => s.RIP = 0x105e8f) (movR32R32Effect 0x105e8f 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105e8f 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105e8f 0xc8 (by decide)) pre_rip
  have f450 : InstrSpec 0x105e91 [0xD1, 0xE8] (fun s => s.RIP = 0x105e91) (shrR32Effect 0x105e91 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105e91 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105e91 0xe8 (by decide) (by decide)) pre_rip
  have f451 : InstrSpec 0x105e93 [0x31, 0xC8] (fun s => s.RIP = 0x105e93) (xorR32R32Effect 0x105e93 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e93 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105e93 0xc8 (by decide)) pre_rip
  have f452 : InstrSpec 0x105e95 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105e95) (andEaxImm32Effect 0x105e95 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105e95 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105e95 0x5050) pre_rip
  have f453 : InstrSpec 0x105e9a [0x31, 0xC1] (fun s => s.RIP = 0x105e9a) (xorR32R32Effect 0x105e9a 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e9a 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105e9a 0xc1 (by decide)) pre_rip
  have f454 : InstrSpec 0x105e9c [0x01, 0xC0] (fun s => s.RIP = 0x105e9c) (addR32R32Effect 0x105e9c 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105e9c 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105e9c 0xc0 (by decide)) pre_rip
  have f455 : InstrSpec 0x105e9e [0x31, 0xC8] (fun s => s.RIP = 0x105e9e) (xorR32R32Effect 0x105e9e 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e9e 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105e9e 0xc8 (by decide)) pre_rip
  have f456 : InstrSpec 0x105ea0 [0x66, 0x89, 0x44, 0x24, 0x6A] (StorePre 0x105ea0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6a)) s (0x105ea0 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105ea0 5 0 (.sib 4 none 0 (.d8 0x6a)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105ea0 5 0 (.sib 4 none 0 (.d8 0x6a))).toInstrSpec (mov_m16_r16_effect_step 0x105ea0 0 (.sib 4 none 0 (.d8 0x6a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f457 : InstrSpec 0x105ea5 [0x0F, 0xB7, 0x44, 0x24, 0x6C] (LoadPre 0x105ea5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x105ea5 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105ea5 5 0 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105ea5 5 0 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (movzx_r32_m16_effect_step 0x105ea5 0 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f458 : InstrSpec 0x105eaa [0x89, 0xC1] (fun s => s.RIP = 0x105eaa) (movR32R32Effect 0x105eaa 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105eaa 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105eaa 0xc1 (by decide)) pre_rip
  have f459 : InstrSpec 0x105eac [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105eac) (shrR32Effect 0x105eac 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105eac 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105eac 0xe9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 902) (RestInside.exec (n := 902) (ρ' := [(0, 900), (1, 896), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e76) f440 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 903) (RestInside.out (n := 903) f441 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 904) (ρ' := [(0, 903), (1, 896), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e7b) f441 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 905) (RestInside.out (n := 905) f442 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 906) (ρ' := [(0, 903), (1, 905), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e7d) f442 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 907) (RestInside.out (n := 907) f443 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 908) (ρ' := [(0, 903), (1, 907), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e80) f443 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 909) (RestInside.out (n := 909) f444 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 910) (ρ' := [(0, 903), (1, 909), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e82) f444 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 911) (RestInside.out (n := 911) f445 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 912) (ρ' := [(0, 903), (1, 911), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e88) f445 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 913) (RestInside.out (n := 913) f446 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 914) (ρ' := [(0, 913), (1, 911), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e8a) f446 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 915) (RestInside.out (n := 915) f447 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 916) (ρ' := [(0, 913), (1, 915), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e8d) f447 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 917) (RestInside.out (n := 917) f448 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 918) (ρ' := [(0, 913), (1, 917), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e8f) f448 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 919) (RestInside.out (n := 919) f449 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 920) (ρ' := [(0, 919), (1, 917), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e91) f449 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 921) (RestInside.out (n := 921) f450 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 922) (ρ' := [(0, 921), (1, 917), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e93) f450 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 923) (RestInside.out (n := 923) f451 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 924) (ρ' := [(0, 923), (1, 917), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e95) f451 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 925) (RestInside.out (n := 925) f452 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 926) (ρ' := [(0, 925), (1, 917), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e9a) f452 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 927) (RestInside.out (n := 927) f453 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 928) (ρ' := [(0, 925), (1, 927), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e9c) f453 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 929) (RestInside.out (n := 929) f454 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 930) (ρ' := [(0, 929), (1, 927), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e9e) f454 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 931) (RestInside.out (n := 931) f455 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 932) (ρ' := [(0, 931), (1, 927), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ea0) f455 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 933) (RestInside.exec (n := 933) (ρ' := [(0, 931), (1, 927), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ea5) f456 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 934) (RestInside.out (n := 934) f457 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 935) (ρ' := [(0, 934), (1, 927), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105eaa) f457 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 936) (RestInside.out (n := 936) f458 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 937) (ρ' := [(0, 934), (1, 936), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105eac) f458 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 938) (RestInside.out (n := 938) f459 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 939) (ρ' := [(0, 934), (1, 938), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105eaf) f459 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_23 code

theorem rest_l10593a_21 [Bindings] (code : CodeMap) :
    Rest (n := 863) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 861), (1, 855), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      772 0x105e37 bytes_l10593a_21 b_l10593a_21 := by
  have f420 : InstrSpec 0x105e37 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105e37) (andEaxImm32Effect 0x105e37 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105e37 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105e37 0x5050) pre_rip
  have f421 : InstrSpec 0x105e3c [0x31, 0xC1] (fun s => s.RIP = 0x105e3c) (xorR32R32Effect 0x105e3c 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e3c 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105e3c 0xc1 (by decide)) pre_rip
  have f422 : InstrSpec 0x105e3e [0x01, 0xC0] (fun s => s.RIP = 0x105e3e) (addR32R32Effect 0x105e3e 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105e3e 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105e3e 0xc0 (by decide)) pre_rip
  have f423 : InstrSpec 0x105e40 [0x31, 0xC8] (fun s => s.RIP = 0x105e40) (xorR32R32Effect 0x105e40 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e40 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105e40 0xc8 (by decide)) pre_rip
  have f424 : InstrSpec 0x105e42 [0x66, 0x89, 0x44, 0x24, 0x66] (StorePre 0x105e42 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x105e42 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105e42 5 0 (.sib 4 none 0 (.d8 0x66)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105e42 5 0 (.sib 4 none 0 (.d8 0x66))).toInstrSpec (mov_m16_r16_effect_step 0x105e42 0 (.sib 4 none 0 (.d8 0x66)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f425 : InstrSpec 0x105e47 [0x0F, 0xB7, 0x44, 0x24, 0x68] (LoadPre 0x105e47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x105e47 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105e47 5 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105e47 5 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (movzx_r32_m16_effect_step 0x105e47 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f426 : InstrSpec 0x105e4c [0x89, 0xC1] (fun s => s.RIP = 0x105e4c) (movR32R32Effect 0x105e4c 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105e4c 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105e4c 0xc1 (by decide)) pre_rip
  have f427 : InstrSpec 0x105e4e [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105e4e) (shrR32Effect 0x105e4e 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105e4e 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105e4e 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f428 : InstrSpec 0x105e51 [0x31, 0xC1] (fun s => s.RIP = 0x105e51) (xorR32R32Effect 0x105e51 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e51 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105e51 0xc1 (by decide)) pre_rip
  have f429 : InstrSpec 0x105e53 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x105e53) (andR32Imm32Effect 0x105e53 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105e53 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x105e53 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f430 : InstrSpec 0x105e59 [0x31, 0xC8] (fun s => s.RIP = 0x105e59) (xorR32R32Effect 0x105e59 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e59 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105e59 0xc8 (by decide)) pre_rip
  have f431 : InstrSpec 0x105e5b [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105e5b) (shlR32Effect 0x105e5b 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105e5b 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105e5b 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f432 : InstrSpec 0x105e5e [0x31, 0xC1] (fun s => s.RIP = 0x105e5e) (xorR32R32Effect 0x105e5e 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e5e 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105e5e 0xc1 (by decide)) pre_rip
  have f433 : InstrSpec 0x105e60 [0x89, 0xC8] (fun s => s.RIP = 0x105e60) (movR32R32Effect 0x105e60 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105e60 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105e60 0xc8 (by decide)) pre_rip
  have f434 : InstrSpec 0x105e62 [0xD1, 0xE8] (fun s => s.RIP = 0x105e62) (shrR32Effect 0x105e62 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105e62 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105e62 0xe8 (by decide) (by decide)) pre_rip
  have f435 : InstrSpec 0x105e64 [0x31, 0xC8] (fun s => s.RIP = 0x105e64) (xorR32R32Effect 0x105e64 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e64 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105e64 0xc8 (by decide)) pre_rip
  have f436 : InstrSpec 0x105e66 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105e66) (andEaxImm32Effect 0x105e66 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105e66 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105e66 0x5050) pre_rip
  have f437 : InstrSpec 0x105e6b [0x31, 0xC1] (fun s => s.RIP = 0x105e6b) (xorR32R32Effect 0x105e6b 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e6b 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105e6b 0xc1 (by decide)) pre_rip
  have f438 : InstrSpec 0x105e6d [0x01, 0xC0] (fun s => s.RIP = 0x105e6d) (addR32R32Effect 0x105e6d 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105e6d 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105e6d 0xc0 (by decide)) pre_rip
  have f439 : InstrSpec 0x105e6f [0x31, 0xC8] (fun s => s.RIP = 0x105e6f) (xorR32R32Effect 0x105e6f 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e6f 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105e6f 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 863) (RestInside.out (n := 863) f420 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 864) (ρ' := [(0, 863), (1, 855), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e3c) f420 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 865) (RestInside.out (n := 865) f421 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 866) (ρ' := [(0, 863), (1, 865), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e3e) f421 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 867) (RestInside.out (n := 867) f422 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 868) (ρ' := [(0, 867), (1, 865), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e40) f422 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 869) (RestInside.out (n := 869) f423 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 870) (ρ' := [(0, 869), (1, 865), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e42) f423 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 871) (RestInside.exec (n := 871) (ρ' := [(0, 869), (1, 865), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e47) f424 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 872) (RestInside.out (n := 872) f425 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 873) (ρ' := [(0, 872), (1, 865), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e4c) f425 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 874) (RestInside.out (n := 874) f426 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 875) (ρ' := [(0, 872), (1, 874), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e4e) f426 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 876) (RestInside.out (n := 876) f427 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 877) (ρ' := [(0, 872), (1, 876), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e51) f427 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 878) (RestInside.out (n := 878) f428 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 879) (ρ' := [(0, 872), (1, 878), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e53) f428 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 880) (RestInside.out (n := 880) f429 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 881) (ρ' := [(0, 872), (1, 880), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e59) f429 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 882) (RestInside.out (n := 882) f430 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 883) (ρ' := [(0, 882), (1, 880), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e5b) f430 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 884) (RestInside.out (n := 884) f431 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 885) (ρ' := [(0, 882), (1, 884), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e5e) f431 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 886) (RestInside.out (n := 886) f432 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 887) (ρ' := [(0, 882), (1, 886), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e60) f432 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 888) (RestInside.out (n := 888) f433 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 889) (ρ' := [(0, 888), (1, 886), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e62) f433 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 890) (RestInside.out (n := 890) f434 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 891) (ρ' := [(0, 890), (1, 886), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e64) f434 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 892) (RestInside.out (n := 892) f435 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 893) (ρ' := [(0, 892), (1, 886), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e66) f435 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 894) (RestInside.out (n := 894) f436 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 895) (ρ' := [(0, 894), (1, 886), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e6b) f436 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 896) (RestInside.out (n := 896) f437 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 897) (ρ' := [(0, 894), (1, 896), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e6d) f437 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 898) (RestInside.out (n := 898) f438 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 899) (ρ' := [(0, 898), (1, 896), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e6f) f438 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 900) (RestInside.out (n := 900) f439 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 901) (ρ' := [(0, 900), (1, 896), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e71) f439 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_22 code

theorem rest_l10593a_20 [Bindings] (code : CodeMap) :
    Rest (n := 824) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 820), (1, 822), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      792 0x105e00 bytes_l10593a_20 b_l10593a_20 := by
  have f400 : InstrSpec 0x105e00 [0x31, 0xC1] (fun s => s.RIP = 0x105e00) (xorR32R32Effect 0x105e00 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e00 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105e00 0xc1 (by decide)) pre_rip
  have f401 : InstrSpec 0x105e02 [0x89, 0xC8] (fun s => s.RIP = 0x105e02) (movR32R32Effect 0x105e02 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105e02 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105e02 0xc8 (by decide)) pre_rip
  have f402 : InstrSpec 0x105e04 [0xD1, 0xE8] (fun s => s.RIP = 0x105e04) (shrR32Effect 0x105e04 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105e04 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105e04 0xe8 (by decide) (by decide)) pre_rip
  have f403 : InstrSpec 0x105e06 [0x31, 0xC8] (fun s => s.RIP = 0x105e06) (xorR32R32Effect 0x105e06 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e06 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105e06 0xc8 (by decide)) pre_rip
  have f404 : InstrSpec 0x105e08 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105e08) (andEaxImm32Effect 0x105e08 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105e08 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105e08 0x5050) pre_rip
  have f405 : InstrSpec 0x105e0d [0x31, 0xC1] (fun s => s.RIP = 0x105e0d) (xorR32R32Effect 0x105e0d 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e0d 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105e0d 0xc1 (by decide)) pre_rip
  have f406 : InstrSpec 0x105e0f [0x01, 0xC0] (fun s => s.RIP = 0x105e0f) (addR32R32Effect 0x105e0f 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105e0f 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105e0f 0xc0 (by decide)) pre_rip
  have f407 : InstrSpec 0x105e11 [0x31, 0xC8] (fun s => s.RIP = 0x105e11) (xorR32R32Effect 0x105e11 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e11 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105e11 0xc8 (by decide)) pre_rip
  have f408 : InstrSpec 0x105e13 [0x66, 0x89, 0x44, 0x24, 0x64] (StorePre 0x105e13 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x105e13 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105e13 5 0 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105e13 5 0 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (mov_m16_r16_effect_step 0x105e13 0 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f409 : InstrSpec 0x105e18 [0x0F, 0xB7, 0x44, 0x24, 0x66] (LoadPre 0x105e18 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x105e18 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105e18 5 0 (.sib 4 none 0 (.d8 0x66)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105e18 5 0 (.sib 4 none 0 (.d8 0x66))).toInstrSpec (movzx_r32_m16_effect_step 0x105e18 0 (.sib 4 none 0 (.d8 0x66)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f410 : InstrSpec 0x105e1d [0x89, 0xC1] (fun s => s.RIP = 0x105e1d) (movR32R32Effect 0x105e1d 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105e1d 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105e1d 0xc1 (by decide)) pre_rip
  have f411 : InstrSpec 0x105e1f [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105e1f) (shrR32Effect 0x105e1f 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105e1f 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105e1f 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f412 : InstrSpec 0x105e22 [0x31, 0xC1] (fun s => s.RIP = 0x105e22) (xorR32R32Effect 0x105e22 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e22 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105e22 0xc1 (by decide)) pre_rip
  have f413 : InstrSpec 0x105e24 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x105e24) (andR32Imm32Effect 0x105e24 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105e24 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x105e24 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f414 : InstrSpec 0x105e2a [0x31, 0xC8] (fun s => s.RIP = 0x105e2a) (xorR32R32Effect 0x105e2a 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e2a 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105e2a 0xc8 (by decide)) pre_rip
  have f415 : InstrSpec 0x105e2c [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105e2c) (shlR32Effect 0x105e2c 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105e2c 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105e2c 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f416 : InstrSpec 0x105e2f [0x31, 0xC1] (fun s => s.RIP = 0x105e2f) (xorR32R32Effect 0x105e2f 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e2f 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105e2f 0xc1 (by decide)) pre_rip
  have f417 : InstrSpec 0x105e31 [0x89, 0xC8] (fun s => s.RIP = 0x105e31) (movR32R32Effect 0x105e31 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105e31 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105e31 0xc8 (by decide)) pre_rip
  have f418 : InstrSpec 0x105e33 [0xD1, 0xE8] (fun s => s.RIP = 0x105e33) (shrR32Effect 0x105e33 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105e33 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105e33 0xe8 (by decide) (by decide)) pre_rip
  have f419 : InstrSpec 0x105e35 [0x31, 0xC8] (fun s => s.RIP = 0x105e35) (xorR32R32Effect 0x105e35 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105e35 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105e35 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 824) (RestInside.out (n := 824) f400 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 825) (ρ' := [(0, 820), (1, 824), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e02) f400 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 826) (RestInside.out (n := 826) f401 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 827) (ρ' := [(0, 826), (1, 824), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e04) f401 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 828) (RestInside.out (n := 828) f402 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 829) (ρ' := [(0, 828), (1, 824), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e06) f402 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 830) (RestInside.out (n := 830) f403 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 831) (ρ' := [(0, 830), (1, 824), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e08) f403 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 832) (RestInside.out (n := 832) f404 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 833) (ρ' := [(0, 832), (1, 824), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e0d) f404 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 834) (RestInside.out (n := 834) f405 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 835) (ρ' := [(0, 832), (1, 834), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e0f) f405 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 836) (RestInside.out (n := 836) f406 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 837) (ρ' := [(0, 836), (1, 834), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e11) f406 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 838) (RestInside.out (n := 838) f407 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 839) (ρ' := [(0, 838), (1, 834), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e13) f407 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 840) (RestInside.exec (n := 840) (ρ' := [(0, 838), (1, 834), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e18) f408 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 841) (RestInside.out (n := 841) f409 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 842) (ρ' := [(0, 841), (1, 834), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e1d) f409 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 843) (RestInside.out (n := 843) f410 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 844) (ρ' := [(0, 841), (1, 843), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e1f) f410 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 845) (RestInside.out (n := 845) f411 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 846) (ρ' := [(0, 841), (1, 845), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e22) f411 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 847) (RestInside.out (n := 847) f412 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 848) (ρ' := [(0, 841), (1, 847), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e24) f412 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 849) (RestInside.out (n := 849) f413 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 850) (ρ' := [(0, 841), (1, 849), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e2a) f413 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 851) (RestInside.out (n := 851) f414 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 852) (ρ' := [(0, 851), (1, 849), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e2c) f414 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 853) (RestInside.out (n := 853) f415 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 854) (ρ' := [(0, 851), (1, 853), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e2f) f415 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 855) (RestInside.out (n := 855) f416 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 856) (ρ' := [(0, 851), (1, 855), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e31) f416 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 857) (RestInside.out (n := 857) f417 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 858) (ρ' := [(0, 857), (1, 855), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e33) f417 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 859) (RestInside.out (n := 859) f418 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 860) (ρ' := [(0, 859), (1, 855), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e35) f418 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 861) (RestInside.out (n := 861) f419 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 862) (ρ' := [(0, 861), (1, 855), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e37) f419 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_21 code

theorem rest_l10593a_19 [Bindings] (code : CodeMap) :
    Rest (n := 785) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 779), (1, 783), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      812 0x105dc4 bytes_l10593a_19 b_l10593a_19 := by
  have f380 : InstrSpec 0x105dc4 [0x31, 0xC1] (fun s => s.RIP = 0x105dc4) (xorR32R32Effect 0x105dc4 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105dc4 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105dc4 0xc1 (by decide)) pre_rip
  have f381 : InstrSpec 0x105dc6 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x105dc6) (andR32Imm32Effect 0x105dc6 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105dc6 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x105dc6 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f382 : InstrSpec 0x105dcc [0x31, 0xC8] (fun s => s.RIP = 0x105dcc) (xorR32R32Effect 0x105dcc 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105dcc 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105dcc 0xc8 (by decide)) pre_rip
  have f383 : InstrSpec 0x105dce [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105dce) (shlR32Effect 0x105dce 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105dce 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105dce 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f384 : InstrSpec 0x105dd1 [0x31, 0xC1] (fun s => s.RIP = 0x105dd1) (xorR32R32Effect 0x105dd1 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105dd1 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105dd1 0xc1 (by decide)) pre_rip
  have f385 : InstrSpec 0x105dd3 [0x89, 0xC8] (fun s => s.RIP = 0x105dd3) (movR32R32Effect 0x105dd3 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105dd3 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105dd3 0xc8 (by decide)) pre_rip
  have f386 : InstrSpec 0x105dd5 [0xD1, 0xE8] (fun s => s.RIP = 0x105dd5) (shrR32Effect 0x105dd5 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105dd5 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105dd5 0xe8 (by decide) (by decide)) pre_rip
  have f387 : InstrSpec 0x105dd7 [0x31, 0xC8] (fun s => s.RIP = 0x105dd7) (xorR32R32Effect 0x105dd7 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105dd7 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105dd7 0xc8 (by decide)) pre_rip
  have f388 : InstrSpec 0x105dd9 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105dd9) (andEaxImm32Effect 0x105dd9 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105dd9 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105dd9 0x5050) pre_rip
  have f389 : InstrSpec 0x105dde [0x31, 0xC1] (fun s => s.RIP = 0x105dde) (xorR32R32Effect 0x105dde 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105dde 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105dde 0xc1 (by decide)) pre_rip
  have f390 : InstrSpec 0x105de0 [0x01, 0xC0] (fun s => s.RIP = 0x105de0) (addR32R32Effect 0x105de0 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105de0 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105de0 0xc0 (by decide)) pre_rip
  have f391 : InstrSpec 0x105de2 [0x31, 0xC8] (fun s => s.RIP = 0x105de2) (xorR32R32Effect 0x105de2 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105de2 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105de2 0xc8 (by decide)) pre_rip
  have f392 : InstrSpec 0x105de4 [0x66, 0x89, 0x44, 0x24, 0x62] (StorePre 0x105de4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x105de4 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105de4 5 0 (.sib 4 none 0 (.d8 0x62)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105de4 5 0 (.sib 4 none 0 (.d8 0x62))).toInstrSpec (mov_m16_r16_effect_step 0x105de4 0 (.sib 4 none 0 (.d8 0x62)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f393 : InstrSpec 0x105de9 [0x0F, 0xB7, 0x44, 0x24, 0x64] (LoadPre 0x105de9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x105de9 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105de9 5 0 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105de9 5 0 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (movzx_r32_m16_effect_step 0x105de9 0 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f394 : InstrSpec 0x105dee [0x89, 0xC1] (fun s => s.RIP = 0x105dee) (movR32R32Effect 0x105dee 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105dee 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105dee 0xc1 (by decide)) pre_rip
  have f395 : InstrSpec 0x105df0 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105df0) (shrR32Effect 0x105df0 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105df0 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105df0 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f396 : InstrSpec 0x105df3 [0x31, 0xC1] (fun s => s.RIP = 0x105df3) (xorR32R32Effect 0x105df3 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105df3 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105df3 0xc1 (by decide)) pre_rip
  have f397 : InstrSpec 0x105df5 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x105df5) (andR32Imm32Effect 0x105df5 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105df5 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x105df5 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f398 : InstrSpec 0x105dfb [0x31, 0xC8] (fun s => s.RIP = 0x105dfb) (xorR32R32Effect 0x105dfb 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105dfb 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105dfb 0xc8 (by decide)) pre_rip
  have f399 : InstrSpec 0x105dfd [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105dfd) (shlR32Effect 0x105dfd 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105dfd 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105dfd 0xe1 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 785) (RestInside.out (n := 785) f380 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 786) (ρ' := [(0, 779), (1, 785), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dc6) f380 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 787) (RestInside.out (n := 787) f381 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 788) (ρ' := [(0, 779), (1, 787), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dcc) f381 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 789) (RestInside.out (n := 789) f382 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 790) (ρ' := [(0, 789), (1, 787), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dce) f382 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 791) (RestInside.out (n := 791) f383 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 792) (ρ' := [(0, 789), (1, 791), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dd1) f383 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 793) (RestInside.out (n := 793) f384 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 794) (ρ' := [(0, 789), (1, 793), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dd3) f384 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 795) (RestInside.out (n := 795) f385 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 796) (ρ' := [(0, 795), (1, 793), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dd5) f385 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 797) (RestInside.out (n := 797) f386 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 798) (ρ' := [(0, 797), (1, 793), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dd7) f386 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 799) (RestInside.out (n := 799) f387 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 800) (ρ' := [(0, 799), (1, 793), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dd9) f387 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 801) (RestInside.out (n := 801) f388 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 802) (ρ' := [(0, 801), (1, 793), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dde) f388 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 803) (RestInside.out (n := 803) f389 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 804) (ρ' := [(0, 801), (1, 803), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105de0) f389 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 805) (RestInside.out (n := 805) f390 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 806) (ρ' := [(0, 805), (1, 803), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105de2) f390 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 807) (RestInside.out (n := 807) f391 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 808) (ρ' := [(0, 807), (1, 803), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105de4) f391 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 809) (RestInside.exec (n := 809) (ρ' := [(0, 807), (1, 803), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105de9) f392 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 810) (RestInside.out (n := 810) f393 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 811) (ρ' := [(0, 810), (1, 803), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dee) f393 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 812) (RestInside.out (n := 812) f394 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 813) (ρ' := [(0, 810), (1, 812), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105df0) f394 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 814) (RestInside.out (n := 814) f395 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 815) (ρ' := [(0, 810), (1, 814), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105df3) f395 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 816) (RestInside.out (n := 816) f396 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 817) (ρ' := [(0, 810), (1, 816), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105df5) f396 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 818) (RestInside.out (n := 818) f397 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 819) (ρ' := [(0, 810), (1, 818), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dfb) f397 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 820) (RestInside.out (n := 820) f398 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 821) (ρ' := [(0, 820), (1, 818), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dfd) f398 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 822) (RestInside.out (n := 822) f399 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 823) (ρ' := [(0, 820), (1, 822), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e00) f399 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_20 code

theorem rest_l10593a_18 [Bindings] (code : CodeMap) :
    Rest (n := 747) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 745), (1, 741), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      832 0x105d86 bytes_l10593a_18 b_l10593a_18 := by
  have f360 : InstrSpec 0x105d86 [0x66, 0x89, 0x44, 0x24, 0x5E] (StorePre 0x105d86 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x105d86 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105d86 5 0 (.sib 4 none 0 (.d8 0x5e)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105d86 5 0 (.sib 4 none 0 (.d8 0x5e))).toInstrSpec (mov_m16_r16_effect_step 0x105d86 0 (.sib 4 none 0 (.d8 0x5e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f361 : InstrSpec 0x105d8b [0x0F, 0xB7, 0x44, 0x24, 0x60] (LoadPre 0x105d8b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x105d8b + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105d8b 5 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105d8b 5 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (movzx_r32_m16_effect_step 0x105d8b 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f362 : InstrSpec 0x105d90 [0x89, 0xC1] (fun s => s.RIP = 0x105d90) (movR32R32Effect 0x105d90 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105d90 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105d90 0xc1 (by decide)) pre_rip
  have f363 : InstrSpec 0x105d92 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105d92) (shrR32Effect 0x105d92 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105d92 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105d92 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f364 : InstrSpec 0x105d95 [0x31, 0xC1] (fun s => s.RIP = 0x105d95) (xorR32R32Effect 0x105d95 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d95 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105d95 0xc1 (by decide)) pre_rip
  have f365 : InstrSpec 0x105d97 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x105d97) (andR32Imm32Effect 0x105d97 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105d97 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x105d97 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f366 : InstrSpec 0x105d9d [0x31, 0xC8] (fun s => s.RIP = 0x105d9d) (xorR32R32Effect 0x105d9d 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d9d 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105d9d 0xc8 (by decide)) pre_rip
  have f367 : InstrSpec 0x105d9f [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105d9f) (shlR32Effect 0x105d9f 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105d9f 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105d9f 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f368 : InstrSpec 0x105da2 [0x31, 0xC1] (fun s => s.RIP = 0x105da2) (xorR32R32Effect 0x105da2 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105da2 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105da2 0xc1 (by decide)) pre_rip
  have f369 : InstrSpec 0x105da4 [0x89, 0xC8] (fun s => s.RIP = 0x105da4) (movR32R32Effect 0x105da4 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105da4 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105da4 0xc8 (by decide)) pre_rip
  have f370 : InstrSpec 0x105da6 [0xD1, 0xE8] (fun s => s.RIP = 0x105da6) (shrR32Effect 0x105da6 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105da6 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105da6 0xe8 (by decide) (by decide)) pre_rip
  have f371 : InstrSpec 0x105da8 [0x31, 0xC8] (fun s => s.RIP = 0x105da8) (xorR32R32Effect 0x105da8 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105da8 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105da8 0xc8 (by decide)) pre_rip
  have f372 : InstrSpec 0x105daa [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105daa) (andEaxImm32Effect 0x105daa 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105daa 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105daa 0x5050) pre_rip
  have f373 : InstrSpec 0x105daf [0x31, 0xC1] (fun s => s.RIP = 0x105daf) (xorR32R32Effect 0x105daf 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105daf 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105daf 0xc1 (by decide)) pre_rip
  have f374 : InstrSpec 0x105db1 [0x01, 0xC0] (fun s => s.RIP = 0x105db1) (addR32R32Effect 0x105db1 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105db1 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105db1 0xc0 (by decide)) pre_rip
  have f375 : InstrSpec 0x105db3 [0x31, 0xC8] (fun s => s.RIP = 0x105db3) (xorR32R32Effect 0x105db3 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105db3 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105db3 0xc8 (by decide)) pre_rip
  have f376 : InstrSpec 0x105db5 [0x66, 0x89, 0x44, 0x24, 0x60] (StorePre 0x105db5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x105db5 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105db5 5 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105db5 5 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m16_r16_effect_step 0x105db5 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f377 : InstrSpec 0x105dba [0x0F, 0xB7, 0x44, 0x24, 0x62] (LoadPre 0x105dba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x105dba + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105dba 5 0 (.sib 4 none 0 (.d8 0x62)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105dba 5 0 (.sib 4 none 0 (.d8 0x62))).toInstrSpec (movzx_r32_m16_effect_step 0x105dba 0 (.sib 4 none 0 (.d8 0x62)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f378 : InstrSpec 0x105dbf [0x89, 0xC1] (fun s => s.RIP = 0x105dbf) (movR32R32Effect 0x105dbf 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105dbf 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105dbf 0xc1 (by decide)) pre_rip
  have f379 : InstrSpec 0x105dc1 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105dc1) (shrR32Effect 0x105dc1 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105dc1 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105dc1 0xe9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 747) (RestInside.exec (n := 747) (ρ' := [(0, 745), (1, 741), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d8b) f360 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 748) (RestInside.out (n := 748) f361 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 749) (ρ' := [(0, 748), (1, 741), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d90) f361 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 750) (RestInside.out (n := 750) f362 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 751) (ρ' := [(0, 748), (1, 750), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d92) f362 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 752) (RestInside.out (n := 752) f363 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 753) (ρ' := [(0, 748), (1, 752), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d95) f363 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 754) (RestInside.out (n := 754) f364 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 755) (ρ' := [(0, 748), (1, 754), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d97) f364 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 756) (RestInside.out (n := 756) f365 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 757) (ρ' := [(0, 748), (1, 756), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d9d) f365 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 758) (RestInside.out (n := 758) f366 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 759) (ρ' := [(0, 758), (1, 756), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d9f) f366 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 760) (RestInside.out (n := 760) f367 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 761) (ρ' := [(0, 758), (1, 760), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105da2) f367 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 762) (RestInside.out (n := 762) f368 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 763) (ρ' := [(0, 758), (1, 762), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105da4) f368 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 764) (RestInside.out (n := 764) f369 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 765) (ρ' := [(0, 764), (1, 762), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105da6) f369 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 766) (RestInside.out (n := 766) f370 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 767) (ρ' := [(0, 766), (1, 762), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105da8) f370 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 768) (RestInside.out (n := 768) f371 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 769) (ρ' := [(0, 768), (1, 762), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105daa) f371 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 770) (RestInside.out (n := 770) f372 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 771) (ρ' := [(0, 770), (1, 762), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105daf) f372 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 772) (RestInside.out (n := 772) f373 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 773) (ρ' := [(0, 770), (1, 772), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105db1) f373 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 774) (RestInside.out (n := 774) f374 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 775) (ρ' := [(0, 774), (1, 772), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105db3) f374 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 776) (RestInside.out (n := 776) f375 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 777) (ρ' := [(0, 776), (1, 772), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105db5) f375 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 778) (RestInside.exec (n := 778) (ρ' := [(0, 776), (1, 772), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dba) f376 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 779) (RestInside.out (n := 779) f377 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 780) (ρ' := [(0, 779), (1, 772), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dbf) f377 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 781) (RestInside.out (n := 781) f378 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 782) (ρ' := [(0, 779), (1, 781), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dc1) f378 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 783) (RestInside.out (n := 783) f379 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 784) (ρ' := [(0, 779), (1, 783), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dc4) f379 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_19 code

theorem rest_l10593a_17 [Bindings] (code : CodeMap) :
    Rest (n := 708) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 706), (1, 700), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      852 0x105d4a bytes_l10593a_17 b_l10593a_17 := by
  have f340 : InstrSpec 0x105d4a [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105d4a) (andEaxImm32Effect 0x105d4a 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105d4a 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105d4a 0x5050) pre_rip
  have f341 : InstrSpec 0x105d4f [0x31, 0xC1] (fun s => s.RIP = 0x105d4f) (xorR32R32Effect 0x105d4f 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d4f 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105d4f 0xc1 (by decide)) pre_rip
  have f342 : InstrSpec 0x105d51 [0x01, 0xC0] (fun s => s.RIP = 0x105d51) (addR32R32Effect 0x105d51 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105d51 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105d51 0xc0 (by decide)) pre_rip
  have f343 : InstrSpec 0x105d53 [0x31, 0xC8] (fun s => s.RIP = 0x105d53) (xorR32R32Effect 0x105d53 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d53 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105d53 0xc8 (by decide)) pre_rip
  have f344 : InstrSpec 0x105d55 [0x89, 0x84, 0x24, 0x04, 0x01, 0x00, 0x00] (StorePre 0x105d55 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x104)) s (0x105d55 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105d55 0 (.sib 4 none 0 (.d32 0x104)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x105d55 0 (.sib 4 none 0 (.d32 0x104))).toInstrSpec (mov_m32_r32_low_effect_step 0x105d55 0 (.sib 4 none 0 (.d32 0x104)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f345 : InstrSpec 0x105d5c [0x0F, 0xB7, 0x44, 0x24, 0x5E] (LoadPre 0x105d5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x105d5c + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105d5c 5 0 (.sib 4 none 0 (.d8 0x5e)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105d5c 5 0 (.sib 4 none 0 (.d8 0x5e))).toInstrSpec (movzx_r32_m16_effect_step 0x105d5c 0 (.sib 4 none 0 (.d8 0x5e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f346 : InstrSpec 0x105d61 [0x89, 0xC1] (fun s => s.RIP = 0x105d61) (movR32R32Effect 0x105d61 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105d61 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105d61 0xc1 (by decide)) pre_rip
  have f347 : InstrSpec 0x105d63 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105d63) (shrR32Effect 0x105d63 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105d63 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105d63 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f348 : InstrSpec 0x105d66 [0x31, 0xC1] (fun s => s.RIP = 0x105d66) (xorR32R32Effect 0x105d66 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d66 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105d66 0xc1 (by decide)) pre_rip
  have f349 : InstrSpec 0x105d68 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x105d68) (andR32Imm32Effect 0x105d68 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105d68 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x105d68 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f350 : InstrSpec 0x105d6e [0x31, 0xC8] (fun s => s.RIP = 0x105d6e) (xorR32R32Effect 0x105d6e 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d6e 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105d6e 0xc8 (by decide)) pre_rip
  have f351 : InstrSpec 0x105d70 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105d70) (shlR32Effect 0x105d70 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105d70 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105d70 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f352 : InstrSpec 0x105d73 [0x31, 0xC1] (fun s => s.RIP = 0x105d73) (xorR32R32Effect 0x105d73 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d73 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105d73 0xc1 (by decide)) pre_rip
  have f353 : InstrSpec 0x105d75 [0x89, 0xC8] (fun s => s.RIP = 0x105d75) (movR32R32Effect 0x105d75 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105d75 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105d75 0xc8 (by decide)) pre_rip
  have f354 : InstrSpec 0x105d77 [0xD1, 0xE8] (fun s => s.RIP = 0x105d77) (shrR32Effect 0x105d77 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105d77 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105d77 0xe8 (by decide) (by decide)) pre_rip
  have f355 : InstrSpec 0x105d79 [0x31, 0xC8] (fun s => s.RIP = 0x105d79) (xorR32R32Effect 0x105d79 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d79 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105d79 0xc8 (by decide)) pre_rip
  have f356 : InstrSpec 0x105d7b [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105d7b) (andEaxImm32Effect 0x105d7b 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105d7b 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105d7b 0x5050) pre_rip
  have f357 : InstrSpec 0x105d80 [0x31, 0xC1] (fun s => s.RIP = 0x105d80) (xorR32R32Effect 0x105d80 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d80 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105d80 0xc1 (by decide)) pre_rip
  have f358 : InstrSpec 0x105d82 [0x01, 0xC0] (fun s => s.RIP = 0x105d82) (addR32R32Effect 0x105d82 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105d82 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105d82 0xc0 (by decide)) pre_rip
  have f359 : InstrSpec 0x105d84 [0x31, 0xC8] (fun s => s.RIP = 0x105d84) (xorR32R32Effect 0x105d84 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d84 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105d84 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 708) (RestInside.out (n := 708) f340 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 709) (ρ' := [(0, 708), (1, 700), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d4f) f340 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 710) (RestInside.out (n := 710) f341 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 711) (ρ' := [(0, 708), (1, 710), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d51) f341 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 712) (RestInside.out (n := 712) f342 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 713) (ρ' := [(0, 712), (1, 710), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d53) f342 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 714) (RestInside.out (n := 714) f343 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 715) (ρ' := [(0, 714), (1, 710), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d55) f343 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 716) (RestInside.exec (n := 716) (ρ' := [(0, 714), (1, 710), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d5c) f344 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 717) (RestInside.out (n := 717) f345 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 718) (ρ' := [(0, 717), (1, 710), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d61) f345 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 719) (RestInside.out (n := 719) f346 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 720) (ρ' := [(0, 717), (1, 719), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d63) f346 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 721) (RestInside.out (n := 721) f347 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 722) (ρ' := [(0, 717), (1, 721), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d66) f347 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 723) (RestInside.out (n := 723) f348 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 724) (ρ' := [(0, 717), (1, 723), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d68) f348 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 725) (RestInside.out (n := 725) f349 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 726) (ρ' := [(0, 717), (1, 725), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d6e) f349 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 727) (RestInside.out (n := 727) f350 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 728) (ρ' := [(0, 727), (1, 725), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d70) f350 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 729) (RestInside.out (n := 729) f351 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 730) (ρ' := [(0, 727), (1, 729), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d73) f351 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 731) (RestInside.out (n := 731) f352 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 732) (ρ' := [(0, 727), (1, 731), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d75) f352 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 733) (RestInside.out (n := 733) f353 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 734) (ρ' := [(0, 733), (1, 731), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d77) f353 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 735) (RestInside.out (n := 735) f354 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 736) (ρ' := [(0, 735), (1, 731), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d79) f354 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 737) (RestInside.out (n := 737) f355 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 738) (ρ' := [(0, 737), (1, 731), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d7b) f355 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 739) (RestInside.out (n := 739) f356 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 740) (ρ' := [(0, 739), (1, 731), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d80) f356 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 741) (RestInside.out (n := 741) f357 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 742) (ρ' := [(0, 739), (1, 741), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d82) f357 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 743) (RestInside.out (n := 743) f358 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 744) (ρ' := [(0, 743), (1, 741), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d84) f358 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 745) (RestInside.out (n := 745) f359 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 746) (ρ' := [(0, 745), (1, 741), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d86) f359 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_18 code

theorem rest_l10593a_16 [Bindings] (code : CodeMap) :
    Rest (n := 669) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 665), (1, 667), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      872 0x105d13 bytes_l10593a_16 b_l10593a_16 := by
  have f320 : InstrSpec 0x105d13 [0x31, 0xC1] (fun s => s.RIP = 0x105d13) (xorR32R32Effect 0x105d13 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d13 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105d13 0xc1 (by decide)) pre_rip
  have f321 : InstrSpec 0x105d15 [0x89, 0xC8] (fun s => s.RIP = 0x105d15) (movR32R32Effect 0x105d15 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105d15 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105d15 0xc8 (by decide)) pre_rip
  have f322 : InstrSpec 0x105d17 [0xD1, 0xE8] (fun s => s.RIP = 0x105d17) (shrR32Effect 0x105d17 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105d17 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105d17 0xe8 (by decide) (by decide)) pre_rip
  have f323 : InstrSpec 0x105d19 [0x31, 0xC8] (fun s => s.RIP = 0x105d19) (xorR32R32Effect 0x105d19 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d19 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105d19 0xc8 (by decide)) pre_rip
  have f324 : InstrSpec 0x105d1b [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105d1b) (andEaxImm32Effect 0x105d1b 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105d1b 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105d1b 0x5050) pre_rip
  have f325 : InstrSpec 0x105d20 [0x31, 0xC1] (fun s => s.RIP = 0x105d20) (xorR32R32Effect 0x105d20 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d20 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105d20 0xc1 (by decide)) pre_rip
  have f326 : InstrSpec 0x105d22 [0x01, 0xC0] (fun s => s.RIP = 0x105d22) (addR32R32Effect 0x105d22 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105d22 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105d22 0xc0 (by decide)) pre_rip
  have f327 : InstrSpec 0x105d24 [0x31, 0xC8] (fun s => s.RIP = 0x105d24) (xorR32R32Effect 0x105d24 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d24 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105d24 0xc8 (by decide)) pre_rip
  have f328 : InstrSpec 0x105d26 [0x66, 0x89, 0x44, 0x24, 0x4A] (StorePre 0x105d26 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x105d26 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105d26 5 0 (.sib 4 none 0 (.d8 0x4a)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105d26 5 0 (.sib 4 none 0 (.d8 0x4a))).toInstrSpec (mov_m16_r16_effect_step 0x105d26 0 (.sib 4 none 0 (.d8 0x4a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f329 : InstrSpec 0x105d2b [0x0F, 0xB7, 0x44, 0x24, 0x5C] (LoadPre 0x105d2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x105d2b + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105d2b 5 0 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105d2b 5 0 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (movzx_r32_m16_effect_step 0x105d2b 0 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f330 : InstrSpec 0x105d30 [0x89, 0xC1] (fun s => s.RIP = 0x105d30) (movR32R32Effect 0x105d30 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105d30 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105d30 0xc1 (by decide)) pre_rip
  have f331 : InstrSpec 0x105d32 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105d32) (shrR32Effect 0x105d32 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105d32 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105d32 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f332 : InstrSpec 0x105d35 [0x31, 0xC1] (fun s => s.RIP = 0x105d35) (xorR32R32Effect 0x105d35 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d35 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105d35 0xc1 (by decide)) pre_rip
  have f333 : InstrSpec 0x105d37 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x105d37) (andR32Imm32Effect 0x105d37 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105d37 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x105d37 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f334 : InstrSpec 0x105d3d [0x31, 0xC8] (fun s => s.RIP = 0x105d3d) (xorR32R32Effect 0x105d3d 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d3d 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105d3d 0xc8 (by decide)) pre_rip
  have f335 : InstrSpec 0x105d3f [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105d3f) (shlR32Effect 0x105d3f 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105d3f 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105d3f 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f336 : InstrSpec 0x105d42 [0x31, 0xC1] (fun s => s.RIP = 0x105d42) (xorR32R32Effect 0x105d42 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d42 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105d42 0xc1 (by decide)) pre_rip
  have f337 : InstrSpec 0x105d44 [0x89, 0xC8] (fun s => s.RIP = 0x105d44) (movR32R32Effect 0x105d44 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105d44 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105d44 0xc8 (by decide)) pre_rip
  have f338 : InstrSpec 0x105d46 [0xD1, 0xE8] (fun s => s.RIP = 0x105d46) (shrR32Effect 0x105d46 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105d46 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105d46 0xe8 (by decide) (by decide)) pre_rip
  have f339 : InstrSpec 0x105d48 [0x31, 0xC8] (fun s => s.RIP = 0x105d48) (xorR32R32Effect 0x105d48 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d48 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105d48 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 669) (RestInside.out (n := 669) f320 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 670) (ρ' := [(0, 665), (1, 669), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d15) f320 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 671) (RestInside.out (n := 671) f321 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 672) (ρ' := [(0, 671), (1, 669), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d17) f321 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 673) (RestInside.out (n := 673) f322 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 674) (ρ' := [(0, 673), (1, 669), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d19) f322 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 675) (RestInside.out (n := 675) f323 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 676) (ρ' := [(0, 675), (1, 669), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d1b) f323 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 677) (RestInside.out (n := 677) f324 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 678) (ρ' := [(0, 677), (1, 669), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d20) f324 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 679) (RestInside.out (n := 679) f325 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 680) (ρ' := [(0, 677), (1, 679), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d22) f325 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 681) (RestInside.out (n := 681) f326 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 682) (ρ' := [(0, 681), (1, 679), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d24) f326 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 683) (RestInside.out (n := 683) f327 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 684) (ρ' := [(0, 683), (1, 679), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d26) f327 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 685) (RestInside.exec (n := 685) (ρ' := [(0, 683), (1, 679), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d2b) f328 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 686) (RestInside.out (n := 686) f329 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 687) (ρ' := [(0, 686), (1, 679), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d30) f329 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 688) (RestInside.out (n := 688) f330 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 689) (ρ' := [(0, 686), (1, 688), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d32) f330 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 690) (RestInside.out (n := 690) f331 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 691) (ρ' := [(0, 686), (1, 690), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d35) f331 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 692) (RestInside.out (n := 692) f332 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 693) (ρ' := [(0, 686), (1, 692), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d37) f332 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 694) (RestInside.out (n := 694) f333 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 695) (ρ' := [(0, 686), (1, 694), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d3d) f333 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 696) (RestInside.out (n := 696) f334 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 697) (ρ' := [(0, 696), (1, 694), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d3f) f334 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 698) (RestInside.out (n := 698) f335 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 699) (ρ' := [(0, 696), (1, 698), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d42) f335 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 700) (RestInside.out (n := 700) f336 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 701) (ρ' := [(0, 696), (1, 700), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d44) f336 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 702) (RestInside.out (n := 702) f337 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 703) (ρ' := [(0, 702), (1, 700), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d46) f337 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 704) (RestInside.out (n := 704) f338 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 705) (ρ' := [(0, 704), (1, 700), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d48) f338 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 706) (RestInside.out (n := 706) f339 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 707) (ρ' := [(0, 706), (1, 700), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d4a) f339 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_17 code

theorem rest_l10593a_15 [Bindings] (code : CodeMap) :
    Rest (n := 630) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 624), (1, 628), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      892 0x105cd7 bytes_l10593a_15 b_l10593a_15 := by
  have f300 : InstrSpec 0x105cd7 [0x31, 0xC1] (fun s => s.RIP = 0x105cd7) (xorR32R32Effect 0x105cd7 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105cd7 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105cd7 0xc1 (by decide)) pre_rip
  have f301 : InstrSpec 0x105cd9 [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x105cd9) (andR32Imm32Effect 0x105cd9 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105cd9 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x105cd9 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f302 : InstrSpec 0x105cdf [0x31, 0xC8] (fun s => s.RIP = 0x105cdf) (xorR32R32Effect 0x105cdf 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105cdf 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105cdf 0xc8 (by decide)) pre_rip
  have f303 : InstrSpec 0x105ce1 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105ce1) (shlR32Effect 0x105ce1 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105ce1 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105ce1 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f304 : InstrSpec 0x105ce4 [0x31, 0xC1] (fun s => s.RIP = 0x105ce4) (xorR32R32Effect 0x105ce4 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105ce4 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105ce4 0xc1 (by decide)) pre_rip
  have f305 : InstrSpec 0x105ce6 [0x89, 0xC8] (fun s => s.RIP = 0x105ce6) (movR32R32Effect 0x105ce6 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105ce6 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105ce6 0xc8 (by decide)) pre_rip
  have f306 : InstrSpec 0x105ce8 [0xD1, 0xE8] (fun s => s.RIP = 0x105ce8) (shrR32Effect 0x105ce8 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105ce8 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105ce8 0xe8 (by decide) (by decide)) pre_rip
  have f307 : InstrSpec 0x105cea [0x31, 0xC8] (fun s => s.RIP = 0x105cea) (xorR32R32Effect 0x105cea 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105cea 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105cea 0xc8 (by decide)) pre_rip
  have f308 : InstrSpec 0x105cec [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105cec) (andEaxImm32Effect 0x105cec 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105cec 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105cec 0x5050) pre_rip
  have f309 : InstrSpec 0x105cf1 [0x31, 0xC1] (fun s => s.RIP = 0x105cf1) (xorR32R32Effect 0x105cf1 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105cf1 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105cf1 0xc1 (by decide)) pre_rip
  have f310 : InstrSpec 0x105cf3 [0x01, 0xC0] (fun s => s.RIP = 0x105cf3) (addR32R32Effect 0x105cf3 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105cf3 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105cf3 0xc0 (by decide)) pre_rip
  have f311 : InstrSpec 0x105cf5 [0x31, 0xC8] (fun s => s.RIP = 0x105cf5) (xorR32R32Effect 0x105cf5 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105cf5 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105cf5 0xc8 (by decide)) pre_rip
  have f312 : InstrSpec 0x105cf7 [0x66, 0x89, 0x44, 0x24, 0x48] (StorePre 0x105cf7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x105cf7 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105cf7 5 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105cf7 5 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m16_r16_effect_step 0x105cf7 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f313 : InstrSpec 0x105cfc [0x0F, 0xB7, 0x44, 0x24, 0x4A] (LoadPre 0x105cfc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x105cfc + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105cfc 5 0 (.sib 4 none 0 (.d8 0x4a)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105cfc 5 0 (.sib 4 none 0 (.d8 0x4a))).toInstrSpec (movzx_r32_m16_effect_step 0x105cfc 0 (.sib 4 none 0 (.d8 0x4a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f314 : InstrSpec 0x105d01 [0x89, 0xC1] (fun s => s.RIP = 0x105d01) (movR32R32Effect 0x105d01 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105d01 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105d01 0xc1 (by decide)) pre_rip
  have f315 : InstrSpec 0x105d03 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105d03) (shrR32Effect 0x105d03 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105d03 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105d03 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f316 : InstrSpec 0x105d06 [0x31, 0xC1] (fun s => s.RIP = 0x105d06) (xorR32R32Effect 0x105d06 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d06 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105d06 0xc1 (by decide)) pre_rip
  have f317 : InstrSpec 0x105d08 [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x105d08) (andR32Imm32Effect 0x105d08 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105d08 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x105d08 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f318 : InstrSpec 0x105d0e [0x31, 0xC8] (fun s => s.RIP = 0x105d0e) (xorR32R32Effect 0x105d0e 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105d0e 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105d0e 0xc8 (by decide)) pre_rip
  have f319 : InstrSpec 0x105d10 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105d10) (shlR32Effect 0x105d10 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105d10 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105d10 0xe1 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 630) (RestInside.out (n := 630) f300 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 631) (ρ' := [(0, 624), (1, 630), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cd9) f300 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 632) (RestInside.out (n := 632) f301 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 633) (ρ' := [(0, 624), (1, 632), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cdf) f301 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 634) (RestInside.out (n := 634) f302 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 635) (ρ' := [(0, 634), (1, 632), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ce1) f302 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 636) (RestInside.out (n := 636) f303 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 637) (ρ' := [(0, 634), (1, 636), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ce4) f303 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 638) (RestInside.out (n := 638) f304 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 639) (ρ' := [(0, 634), (1, 638), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ce6) f304 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 640) (RestInside.out (n := 640) f305 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 641) (ρ' := [(0, 640), (1, 638), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ce8) f305 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 642) (RestInside.out (n := 642) f306 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 643) (ρ' := [(0, 642), (1, 638), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cea) f306 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 644) (RestInside.out (n := 644) f307 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 645) (ρ' := [(0, 644), (1, 638), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cec) f307 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 646) (RestInside.out (n := 646) f308 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 647) (ρ' := [(0, 646), (1, 638), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cf1) f308 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 648) (RestInside.out (n := 648) f309 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 649) (ρ' := [(0, 646), (1, 648), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cf3) f309 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 650) (RestInside.out (n := 650) f310 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 651) (ρ' := [(0, 650), (1, 648), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cf5) f310 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 652) (RestInside.out (n := 652) f311 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 653) (ρ' := [(0, 652), (1, 648), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cf7) f311 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 654) (RestInside.exec (n := 654) (ρ' := [(0, 652), (1, 648), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cfc) f312 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 655) (RestInside.out (n := 655) f313 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 656) (ρ' := [(0, 655), (1, 648), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d01) f313 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 657) (RestInside.out (n := 657) f314 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 658) (ρ' := [(0, 655), (1, 657), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d03) f314 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 659) (RestInside.out (n := 659) f315 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 660) (ρ' := [(0, 655), (1, 659), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d06) f315 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 661) (RestInside.out (n := 661) f316 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 662) (ρ' := [(0, 655), (1, 661), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d08) f316 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 663) (RestInside.out (n := 663) f317 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 664) (ρ' := [(0, 655), (1, 663), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d0e) f317 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 665) (RestInside.out (n := 665) f318 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 666) (ρ' := [(0, 665), (1, 663), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d10) f318 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 667) (RestInside.out (n := 667) f319 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 668) (ρ' := [(0, 665), (1, 667), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d13) f319 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_16 code

theorem rest_l10593a_14 [Bindings] (code : CodeMap) :
    Rest (n := 592) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 590), (1, 586), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      912 0x105c99 bytes_l10593a_14 b_l10593a_14 := by
  have f280 : InstrSpec 0x105c99 [0x66, 0x89, 0x44, 0x24, 0x44] (StorePre 0x105c99 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x105c99 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105c99 5 0 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105c99 5 0 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_m16_r16_effect_step 0x105c99 0 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f281 : InstrSpec 0x105c9e [0x0F, 0xB7, 0x44, 0x24, 0x46] (LoadPre 0x105c9e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x105c9e + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105c9e 5 0 (.sib 4 none 0 (.d8 0x46)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105c9e 5 0 (.sib 4 none 0 (.d8 0x46))).toInstrSpec (movzx_r32_m16_effect_step 0x105c9e 0 (.sib 4 none 0 (.d8 0x46)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f282 : InstrSpec 0x105ca3 [0x89, 0xC1] (fun s => s.RIP = 0x105ca3) (movR32R32Effect 0x105ca3 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105ca3 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105ca3 0xc1 (by decide)) pre_rip
  have f283 : InstrSpec 0x105ca5 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105ca5) (shrR32Effect 0x105ca5 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105ca5 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105ca5 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f284 : InstrSpec 0x105ca8 [0x31, 0xC1] (fun s => s.RIP = 0x105ca8) (xorR32R32Effect 0x105ca8 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105ca8 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105ca8 0xc1 (by decide)) pre_rip
  have f285 : InstrSpec 0x105caa [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x105caa) (andR32Imm32Effect 0x105caa 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105caa 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x105caa 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f286 : InstrSpec 0x105cb0 [0x31, 0xC8] (fun s => s.RIP = 0x105cb0) (xorR32R32Effect 0x105cb0 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105cb0 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105cb0 0xc8 (by decide)) pre_rip
  have f287 : InstrSpec 0x105cb2 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105cb2) (shlR32Effect 0x105cb2 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105cb2 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105cb2 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f288 : InstrSpec 0x105cb5 [0x31, 0xC1] (fun s => s.RIP = 0x105cb5) (xorR32R32Effect 0x105cb5 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105cb5 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105cb5 0xc1 (by decide)) pre_rip
  have f289 : InstrSpec 0x105cb7 [0x89, 0xC8] (fun s => s.RIP = 0x105cb7) (movR32R32Effect 0x105cb7 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105cb7 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105cb7 0xc8 (by decide)) pre_rip
  have f290 : InstrSpec 0x105cb9 [0xD1, 0xE8] (fun s => s.RIP = 0x105cb9) (shrR32Effect 0x105cb9 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105cb9 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105cb9 0xe8 (by decide) (by decide)) pre_rip
  have f291 : InstrSpec 0x105cbb [0x31, 0xC8] (fun s => s.RIP = 0x105cbb) (xorR32R32Effect 0x105cbb 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105cbb 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105cbb 0xc8 (by decide)) pre_rip
  have f292 : InstrSpec 0x105cbd [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105cbd) (andEaxImm32Effect 0x105cbd 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105cbd 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105cbd 0x5050) pre_rip
  have f293 : InstrSpec 0x105cc2 [0x31, 0xC1] (fun s => s.RIP = 0x105cc2) (xorR32R32Effect 0x105cc2 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105cc2 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105cc2 0xc1 (by decide)) pre_rip
  have f294 : InstrSpec 0x105cc4 [0x01, 0xC0] (fun s => s.RIP = 0x105cc4) (addR32R32Effect 0x105cc4 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105cc4 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105cc4 0xc0 (by decide)) pre_rip
  have f295 : InstrSpec 0x105cc6 [0x31, 0xC8] (fun s => s.RIP = 0x105cc6) (xorR32R32Effect 0x105cc6 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105cc6 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105cc6 0xc8 (by decide)) pre_rip
  have f296 : InstrSpec 0x105cc8 [0x66, 0x89, 0x44, 0x24, 0x46] (StorePre 0x105cc8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x105cc8 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105cc8 5 0 (.sib 4 none 0 (.d8 0x46)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105cc8 5 0 (.sib 4 none 0 (.d8 0x46))).toInstrSpec (mov_m16_r16_effect_step 0x105cc8 0 (.sib 4 none 0 (.d8 0x46)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f297 : InstrSpec 0x105ccd [0x0F, 0xB7, 0x44, 0x24, 0x48] (LoadPre 0x105ccd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x105ccd + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105ccd 5 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105ccd 5 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (movzx_r32_m16_effect_step 0x105ccd 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f298 : InstrSpec 0x105cd2 [0x89, 0xC1] (fun s => s.RIP = 0x105cd2) (movR32R32Effect 0x105cd2 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105cd2 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105cd2 0xc1 (by decide)) pre_rip
  have f299 : InstrSpec 0x105cd4 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105cd4) (shrR32Effect 0x105cd4 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105cd4 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105cd4 0xe9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 592) (RestInside.exec (n := 592) (ρ' := [(0, 590), (1, 586), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c9e) f280 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 593) (RestInside.out (n := 593) f281 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 594) (ρ' := [(0, 593), (1, 586), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ca3) f281 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 595) (RestInside.out (n := 595) f282 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 596) (ρ' := [(0, 593), (1, 595), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ca5) f282 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 597) (RestInside.out (n := 597) f283 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 598) (ρ' := [(0, 593), (1, 597), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ca8) f283 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 599) (RestInside.out (n := 599) f284 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 600) (ρ' := [(0, 593), (1, 599), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105caa) f284 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 601) (RestInside.out (n := 601) f285 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 602) (ρ' := [(0, 593), (1, 601), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cb0) f285 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 603) (RestInside.out (n := 603) f286 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 604) (ρ' := [(0, 603), (1, 601), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cb2) f286 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 605) (RestInside.out (n := 605) f287 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 606) (ρ' := [(0, 603), (1, 605), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cb5) f287 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 607) (RestInside.out (n := 607) f288 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 608) (ρ' := [(0, 603), (1, 607), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cb7) f288 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 609) (RestInside.out (n := 609) f289 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 610) (ρ' := [(0, 609), (1, 607), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cb9) f289 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 611) (RestInside.out (n := 611) f290 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 612) (ρ' := [(0, 611), (1, 607), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cbb) f290 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 613) (RestInside.out (n := 613) f291 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 614) (ρ' := [(0, 613), (1, 607), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cbd) f291 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 615) (RestInside.out (n := 615) f292 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 616) (ρ' := [(0, 615), (1, 607), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cc2) f292 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 617) (RestInside.out (n := 617) f293 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 618) (ρ' := [(0, 615), (1, 617), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cc4) f293 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 619) (RestInside.out (n := 619) f294 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 620) (ρ' := [(0, 619), (1, 617), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cc6) f294 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 621) (RestInside.out (n := 621) f295 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 622) (ρ' := [(0, 621), (1, 617), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cc8) f295 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 623) (RestInside.exec (n := 623) (ρ' := [(0, 621), (1, 617), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ccd) f296 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 624) (RestInside.out (n := 624) f297 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 625) (ρ' := [(0, 624), (1, 617), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cd2) f297 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 626) (RestInside.out (n := 626) f298 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 627) (ρ' := [(0, 624), (1, 626), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cd4) f298 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 628) (RestInside.out (n := 628) f299 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 629) (ρ' := [(0, 624), (1, 628), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cd7) f299 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_15 code

theorem rest_l10593a_13 [Bindings] (code : CodeMap) :
    Rest (n := 553) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 551), (1, 545), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      932 0x105c5f bytes_l10593a_13 b_l10593a_13 := by
  have f260 : InstrSpec 0x105c5f [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105c5f) (andEaxImm32Effect 0x105c5f 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105c5f 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105c5f 0x5050) pre_rip
  have f261 : InstrSpec 0x105c64 [0x31, 0xC1] (fun s => s.RIP = 0x105c64) (xorR32R32Effect 0x105c64 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c64 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105c64 0xc1 (by decide)) pre_rip
  have f262 : InstrSpec 0x105c66 [0x01, 0xC0] (fun s => s.RIP = 0x105c66) (addR32R32Effect 0x105c66 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105c66 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105c66 0xc0 (by decide)) pre_rip
  have f263 : InstrSpec 0x105c68 [0x31, 0xC8] (fun s => s.RIP = 0x105c68) (xorR32R32Effect 0x105c68 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c68 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105c68 0xc8 (by decide)) pre_rip
  have f264 : InstrSpec 0x105c6a [0x66, 0x89, 0x44, 0x24, 0x42] (StorePre 0x105c6a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x105c6a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105c6a 5 0 (.sib 4 none 0 (.d8 0x42)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105c6a 5 0 (.sib 4 none 0 (.d8 0x42))).toInstrSpec (mov_m16_r16_effect_step 0x105c6a 0 (.sib 4 none 0 (.d8 0x42)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f265 : InstrSpec 0x105c6f [0x0F, 0xB7, 0x44, 0x24, 0x44] (LoadPre 0x105c6f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x105c6f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105c6f 5 0 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105c6f 5 0 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (movzx_r32_m16_effect_step 0x105c6f 0 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f266 : InstrSpec 0x105c74 [0x89, 0xC1] (fun s => s.RIP = 0x105c74) (movR32R32Effect 0x105c74 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105c74 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105c74 0xc1 (by decide)) pre_rip
  have f267 : InstrSpec 0x105c76 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105c76) (shrR32Effect 0x105c76 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105c76 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105c76 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f268 : InstrSpec 0x105c79 [0x31, 0xC1] (fun s => s.RIP = 0x105c79) (xorR32R32Effect 0x105c79 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c79 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105c79 0xc1 (by decide)) pre_rip
  have f269 : InstrSpec 0x105c7b [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x105c7b) (andR32Imm32Effect 0x105c7b 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105c7b 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x105c7b 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f270 : InstrSpec 0x105c81 [0x31, 0xC8] (fun s => s.RIP = 0x105c81) (xorR32R32Effect 0x105c81 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c81 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105c81 0xc8 (by decide)) pre_rip
  have f271 : InstrSpec 0x105c83 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105c83) (shlR32Effect 0x105c83 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105c83 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105c83 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f272 : InstrSpec 0x105c86 [0x31, 0xC1] (fun s => s.RIP = 0x105c86) (xorR32R32Effect 0x105c86 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c86 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105c86 0xc1 (by decide)) pre_rip
  have f273 : InstrSpec 0x105c88 [0x89, 0xC8] (fun s => s.RIP = 0x105c88) (movR32R32Effect 0x105c88 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105c88 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105c88 0xc8 (by decide)) pre_rip
  have f274 : InstrSpec 0x105c8a [0xD1, 0xE8] (fun s => s.RIP = 0x105c8a) (shrR32Effect 0x105c8a 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105c8a 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105c8a 0xe8 (by decide) (by decide)) pre_rip
  have f275 : InstrSpec 0x105c8c [0x31, 0xC8] (fun s => s.RIP = 0x105c8c) (xorR32R32Effect 0x105c8c 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c8c 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105c8c 0xc8 (by decide)) pre_rip
  have f276 : InstrSpec 0x105c8e [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105c8e) (andEaxImm32Effect 0x105c8e 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105c8e 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105c8e 0x5050) pre_rip
  have f277 : InstrSpec 0x105c93 [0x31, 0xC1] (fun s => s.RIP = 0x105c93) (xorR32R32Effect 0x105c93 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c93 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105c93 0xc1 (by decide)) pre_rip
  have f278 : InstrSpec 0x105c95 [0x01, 0xC0] (fun s => s.RIP = 0x105c95) (addR32R32Effect 0x105c95 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105c95 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105c95 0xc0 (by decide)) pre_rip
  have f279 : InstrSpec 0x105c97 [0x31, 0xC8] (fun s => s.RIP = 0x105c97) (xorR32R32Effect 0x105c97 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c97 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105c97 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 553) (RestInside.out (n := 553) f260 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 554) (ρ' := [(0, 553), (1, 545), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c64) f260 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 555) (RestInside.out (n := 555) f261 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 556) (ρ' := [(0, 553), (1, 555), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c66) f261 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 557) (RestInside.out (n := 557) f262 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 558) (ρ' := [(0, 557), (1, 555), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c68) f262 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 559) (RestInside.out (n := 559) f263 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 560) (ρ' := [(0, 559), (1, 555), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c6a) f263 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 561) (RestInside.exec (n := 561) (ρ' := [(0, 559), (1, 555), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c6f) f264 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 562) (RestInside.out (n := 562) f265 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 563) (ρ' := [(0, 562), (1, 555), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c74) f265 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 564) (RestInside.out (n := 564) f266 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 565) (ρ' := [(0, 562), (1, 564), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c76) f266 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 566) (RestInside.out (n := 566) f267 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 567) (ρ' := [(0, 562), (1, 566), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c79) f267 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 568) (RestInside.out (n := 568) f268 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 569) (ρ' := [(0, 562), (1, 568), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c7b) f268 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 570) (RestInside.out (n := 570) f269 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 571) (ρ' := [(0, 562), (1, 570), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c81) f269 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 572) (RestInside.out (n := 572) f270 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 573) (ρ' := [(0, 572), (1, 570), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c83) f270 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 574) (RestInside.out (n := 574) f271 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 575) (ρ' := [(0, 572), (1, 574), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c86) f271 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 576) (RestInside.out (n := 576) f272 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 577) (ρ' := [(0, 572), (1, 576), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c88) f272 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 578) (RestInside.out (n := 578) f273 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 579) (ρ' := [(0, 578), (1, 576), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c8a) f273 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 580) (RestInside.out (n := 580) f274 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 581) (ρ' := [(0, 580), (1, 576), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c8c) f274 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 582) (RestInside.out (n := 582) f275 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 583) (ρ' := [(0, 582), (1, 576), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c8e) f275 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 584) (RestInside.out (n := 584) f276 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 585) (ρ' := [(0, 584), (1, 576), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c93) f276 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 586) (RestInside.out (n := 586) f277 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 587) (ρ' := [(0, 584), (1, 586), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c95) f277 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 588) (RestInside.out (n := 588) f278 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 589) (ρ' := [(0, 588), (1, 586), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c97) f278 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 590) (RestInside.out (n := 590) f279 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 591) (ρ' := [(0, 590), (1, 586), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c99) f279 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_14 code

theorem rest_l10593a_12 [Bindings] (code : CodeMap) :
    Rest (n := 514) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 510), (1, 512), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      952 0x105c28 bytes_l10593a_12 b_l10593a_12 := by
  have f240 : InstrSpec 0x105c28 [0x31, 0xC1] (fun s => s.RIP = 0x105c28) (xorR32R32Effect 0x105c28 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c28 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105c28 0xc1 (by decide)) pre_rip
  have f241 : InstrSpec 0x105c2a [0x89, 0xC8] (fun s => s.RIP = 0x105c2a) (movR32R32Effect 0x105c2a 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105c2a 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105c2a 0xc8 (by decide)) pre_rip
  have f242 : InstrSpec 0x105c2c [0xD1, 0xE8] (fun s => s.RIP = 0x105c2c) (shrR32Effect 0x105c2c 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105c2c 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105c2c 0xe8 (by decide) (by decide)) pre_rip
  have f243 : InstrSpec 0x105c2e [0x31, 0xC8] (fun s => s.RIP = 0x105c2e) (xorR32R32Effect 0x105c2e 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c2e 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105c2e 0xc8 (by decide)) pre_rip
  have f244 : InstrSpec 0x105c30 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105c30) (andEaxImm32Effect 0x105c30 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105c30 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105c30 0x5050) pre_rip
  have f245 : InstrSpec 0x105c35 [0x31, 0xC1] (fun s => s.RIP = 0x105c35) (xorR32R32Effect 0x105c35 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c35 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105c35 0xc1 (by decide)) pre_rip
  have f246 : InstrSpec 0x105c37 [0x01, 0xC0] (fun s => s.RIP = 0x105c37) (addR32R32Effect 0x105c37 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105c37 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105c37 0xc0 (by decide)) pre_rip
  have f247 : InstrSpec 0x105c39 [0x31, 0xC8] (fun s => s.RIP = 0x105c39) (xorR32R32Effect 0x105c39 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c39 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105c39 0xc8 (by decide)) pre_rip
  have f248 : InstrSpec 0x105c3b [0x66, 0x89, 0x44, 0x24, 0x40] (StorePre 0x105c3b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x105c3b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105c3b 5 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105c3b 5 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m16_r16_effect_step 0x105c3b 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f249 : InstrSpec 0x105c40 [0x0F, 0xB7, 0x44, 0x24, 0x42] (LoadPre 0x105c40 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x105c40 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105c40 5 0 (.sib 4 none 0 (.d8 0x42)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105c40 5 0 (.sib 4 none 0 (.d8 0x42))).toInstrSpec (movzx_r32_m16_effect_step 0x105c40 0 (.sib 4 none 0 (.d8 0x42)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f250 : InstrSpec 0x105c45 [0x89, 0xC1] (fun s => s.RIP = 0x105c45) (movR32R32Effect 0x105c45 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105c45 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105c45 0xc1 (by decide)) pre_rip
  have f251 : InstrSpec 0x105c47 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105c47) (shrR32Effect 0x105c47 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105c47 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105c47 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f252 : InstrSpec 0x105c4a [0x31, 0xC1] (fun s => s.RIP = 0x105c4a) (xorR32R32Effect 0x105c4a 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c4a 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105c4a 0xc1 (by decide)) pre_rip
  have f253 : InstrSpec 0x105c4c [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x105c4c) (andR32Imm32Effect 0x105c4c 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105c4c 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x105c4c 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f254 : InstrSpec 0x105c52 [0x31, 0xC8] (fun s => s.RIP = 0x105c52) (xorR32R32Effect 0x105c52 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c52 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105c52 0xc8 (by decide)) pre_rip
  have f255 : InstrSpec 0x105c54 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105c54) (shlR32Effect 0x105c54 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105c54 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105c54 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f256 : InstrSpec 0x105c57 [0x31, 0xC1] (fun s => s.RIP = 0x105c57) (xorR32R32Effect 0x105c57 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c57 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105c57 0xc1 (by decide)) pre_rip
  have f257 : InstrSpec 0x105c59 [0x89, 0xC8] (fun s => s.RIP = 0x105c59) (movR32R32Effect 0x105c59 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105c59 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105c59 0xc8 (by decide)) pre_rip
  have f258 : InstrSpec 0x105c5b [0xD1, 0xE8] (fun s => s.RIP = 0x105c5b) (shrR32Effect 0x105c5b 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105c5b 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105c5b 0xe8 (by decide) (by decide)) pre_rip
  have f259 : InstrSpec 0x105c5d [0x31, 0xC8] (fun s => s.RIP = 0x105c5d) (xorR32R32Effect 0x105c5d 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c5d 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105c5d 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 514) (RestInside.out (n := 514) f240 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 515) (ρ' := [(0, 510), (1, 514), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c2a) f240 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 516) (RestInside.out (n := 516) f241 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 517) (ρ' := [(0, 516), (1, 514), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c2c) f241 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 518) (RestInside.out (n := 518) f242 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 519) (ρ' := [(0, 518), (1, 514), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c2e) f242 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 520) (RestInside.out (n := 520) f243 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 521) (ρ' := [(0, 520), (1, 514), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c30) f243 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 522) (RestInside.out (n := 522) f244 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 523) (ρ' := [(0, 522), (1, 514), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c35) f244 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 524) (RestInside.out (n := 524) f245 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 525) (ρ' := [(0, 522), (1, 524), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c37) f245 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 526) (RestInside.out (n := 526) f246 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 527) (ρ' := [(0, 526), (1, 524), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c39) f246 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 528) (RestInside.out (n := 528) f247 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 529) (ρ' := [(0, 528), (1, 524), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c3b) f247 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 530) (RestInside.exec (n := 530) (ρ' := [(0, 528), (1, 524), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c40) f248 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 531) (RestInside.out (n := 531) f249 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 532) (ρ' := [(0, 531), (1, 524), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c45) f249 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 533) (RestInside.out (n := 533) f250 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 534) (ρ' := [(0, 531), (1, 533), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c47) f250 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 535) (RestInside.out (n := 535) f251 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 536) (ρ' := [(0, 531), (1, 535), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c4a) f251 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 537) (RestInside.out (n := 537) f252 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 538) (ρ' := [(0, 531), (1, 537), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c4c) f252 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 539) (RestInside.out (n := 539) f253 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 540) (ρ' := [(0, 531), (1, 539), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c52) f253 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 541) (RestInside.out (n := 541) f254 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 542) (ρ' := [(0, 541), (1, 539), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c54) f254 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 543) (RestInside.out (n := 543) f255 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 544) (ρ' := [(0, 541), (1, 543), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c57) f255 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 545) (RestInside.out (n := 545) f256 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 546) (ρ' := [(0, 541), (1, 545), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c59) f256 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 547) (RestInside.out (n := 547) f257 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 548) (ρ' := [(0, 547), (1, 545), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c5b) f257 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 549) (RestInside.out (n := 549) f258 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 550) (ρ' := [(0, 549), (1, 545), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c5d) f258 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 551) (RestInside.out (n := 551) f259 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 552) (ρ' := [(0, 551), (1, 545), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c5f) f259 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_13 code

theorem rest_l10593a_11 [Bindings] (code : CodeMap) :
    Rest (n := 475) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 469), (1, 473), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      972 0x105bec bytes_l10593a_11 b_l10593a_11 := by
  have f220 : InstrSpec 0x105bec [0x31, 0xC1] (fun s => s.RIP = 0x105bec) (xorR32R32Effect 0x105bec 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105bec 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105bec 0xc1 (by decide)) pre_rip
  have f221 : InstrSpec 0x105bee [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x105bee) (andR32Imm32Effect 0x105bee 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105bee 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x105bee 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f222 : InstrSpec 0x105bf4 [0x31, 0xC8] (fun s => s.RIP = 0x105bf4) (xorR32R32Effect 0x105bf4 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105bf4 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105bf4 0xc8 (by decide)) pre_rip
  have f223 : InstrSpec 0x105bf6 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105bf6) (shlR32Effect 0x105bf6 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105bf6 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105bf6 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f224 : InstrSpec 0x105bf9 [0x31, 0xC1] (fun s => s.RIP = 0x105bf9) (xorR32R32Effect 0x105bf9 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105bf9 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105bf9 0xc1 (by decide)) pre_rip
  have f225 : InstrSpec 0x105bfb [0x89, 0xC8] (fun s => s.RIP = 0x105bfb) (movR32R32Effect 0x105bfb 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105bfb 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105bfb 0xc8 (by decide)) pre_rip
  have f226 : InstrSpec 0x105bfd [0xD1, 0xE8] (fun s => s.RIP = 0x105bfd) (shrR32Effect 0x105bfd 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105bfd 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105bfd 0xe8 (by decide) (by decide)) pre_rip
  have f227 : InstrSpec 0x105bff [0x31, 0xC8] (fun s => s.RIP = 0x105bff) (xorR32R32Effect 0x105bff 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105bff 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105bff 0xc8 (by decide)) pre_rip
  have f228 : InstrSpec 0x105c01 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105c01) (andEaxImm32Effect 0x105c01 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105c01 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105c01 0x5050) pre_rip
  have f229 : InstrSpec 0x105c06 [0x31, 0xC1] (fun s => s.RIP = 0x105c06) (xorR32R32Effect 0x105c06 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c06 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105c06 0xc1 (by decide)) pre_rip
  have f230 : InstrSpec 0x105c08 [0x01, 0xC0] (fun s => s.RIP = 0x105c08) (addR32R32Effect 0x105c08 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105c08 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105c08 0xc0 (by decide)) pre_rip
  have f231 : InstrSpec 0x105c0a [0x31, 0xC8] (fun s => s.RIP = 0x105c0a) (xorR32R32Effect 0x105c0a 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c0a 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105c0a 0xc8 (by decide)) pre_rip
  have f232 : InstrSpec 0x105c0c [0x66, 0x89, 0x44, 0x24, 0x3E] (StorePre 0x105c0c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x105c0c + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105c0c 5 0 (.sib 4 none 0 (.d8 0x3e)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105c0c 5 0 (.sib 4 none 0 (.d8 0x3e))).toInstrSpec (mov_m16_r16_effect_step 0x105c0c 0 (.sib 4 none 0 (.d8 0x3e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f233 : InstrSpec 0x105c11 [0x0F, 0xB7, 0x44, 0x24, 0x40] (LoadPre 0x105c11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x105c11 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105c11 5 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105c11 5 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (movzx_r32_m16_effect_step 0x105c11 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f234 : InstrSpec 0x105c16 [0x89, 0xC1] (fun s => s.RIP = 0x105c16) (movR32R32Effect 0x105c16 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105c16 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105c16 0xc1 (by decide)) pre_rip
  have f235 : InstrSpec 0x105c18 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105c18) (shrR32Effect 0x105c18 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105c18 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105c18 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f236 : InstrSpec 0x105c1b [0x31, 0xC1] (fun s => s.RIP = 0x105c1b) (xorR32R32Effect 0x105c1b 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c1b 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105c1b 0xc1 (by decide)) pre_rip
  have f237 : InstrSpec 0x105c1d [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x105c1d) (andR32Imm32Effect 0x105c1d 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105c1d 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x105c1d 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f238 : InstrSpec 0x105c23 [0x31, 0xC8] (fun s => s.RIP = 0x105c23) (xorR32R32Effect 0x105c23 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105c23 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105c23 0xc8 (by decide)) pre_rip
  have f239 : InstrSpec 0x105c25 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105c25) (shlR32Effect 0x105c25 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105c25 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105c25 0xe1 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 475) (RestInside.out (n := 475) f220 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 476) (ρ' := [(0, 469), (1, 475), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bee) f220 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 477) (RestInside.out (n := 477) f221 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 478) (ρ' := [(0, 469), (1, 477), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bf4) f221 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 479) (RestInside.out (n := 479) f222 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 480) (ρ' := [(0, 479), (1, 477), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bf6) f222 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 481) (RestInside.out (n := 481) f223 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 482) (ρ' := [(0, 479), (1, 481), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bf9) f223 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 483) (RestInside.out (n := 483) f224 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 484) (ρ' := [(0, 479), (1, 483), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bfb) f224 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 485) (RestInside.out (n := 485) f225 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 486) (ρ' := [(0, 485), (1, 483), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bfd) f225 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 487) (RestInside.out (n := 487) f226 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 488) (ρ' := [(0, 487), (1, 483), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bff) f226 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 489) (RestInside.out (n := 489) f227 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 490) (ρ' := [(0, 489), (1, 483), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c01) f227 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 491) (RestInside.out (n := 491) f228 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 492) (ρ' := [(0, 491), (1, 483), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c06) f228 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 493) (RestInside.out (n := 493) f229 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 494) (ρ' := [(0, 491), (1, 493), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c08) f229 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 495) (RestInside.out (n := 495) f230 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 496) (ρ' := [(0, 495), (1, 493), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c0a) f230 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 497) (RestInside.out (n := 497) f231 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 498) (ρ' := [(0, 497), (1, 493), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c0c) f231 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 499) (RestInside.exec (n := 499) (ρ' := [(0, 497), (1, 493), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c11) f232 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 500) (RestInside.out (n := 500) f233 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 501) (ρ' := [(0, 500), (1, 493), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c16) f233 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 502) (RestInside.out (n := 502) f234 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 503) (ρ' := [(0, 500), (1, 502), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c18) f234 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 504) (RestInside.out (n := 504) f235 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 505) (ρ' := [(0, 500), (1, 504), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c1b) f235 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 506) (RestInside.out (n := 506) f236 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 507) (ρ' := [(0, 500), (1, 506), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c1d) f236 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 508) (RestInside.out (n := 508) f237 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 509) (ρ' := [(0, 500), (1, 508), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c23) f237 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 510) (RestInside.out (n := 510) f238 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 511) (ρ' := [(0, 510), (1, 508), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c25) f238 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 512) (RestInside.out (n := 512) f239 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 513) (ρ' := [(0, 510), (1, 512), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c28) f239 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_12 code

theorem rest_l10593a_10 [Bindings] (code : CodeMap) :
    Rest (n := 437) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 431), (1, 435), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      992 0x105bac bytes_l10593a_10 b_l10593a_10 := by
  have f200 : InstrSpec 0x105bac [0x66, 0x89, 0x4C, 0x24, 0x3A] (StorePre 0x105bac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x105bac + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105bac 5 1 (.sib 4 none 0 (.d8 0x3a)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105bac 5 1 (.sib 4 none 0 (.d8 0x3a))).toInstrSpec (mov_m16_r16_effect_step 0x105bac 1 (.sib 4 none 0 (.d8 0x3a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f201 : InstrSpec 0x105bb1 [0x0F, 0xB7, 0x44, 0x24, 0x3C] (LoadPre 0x105bb1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x105bb1 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105bb1 5 0 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105bb1 5 0 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (movzx_r32_m16_effect_step 0x105bb1 0 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f202 : InstrSpec 0x105bb6 [0x89, 0xC1] (fun s => s.RIP = 0x105bb6) (movR32R32Effect 0x105bb6 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105bb6 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105bb6 0xc1 (by decide)) pre_rip
  have f203 : InstrSpec 0x105bb8 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105bb8) (shrR32Effect 0x105bb8 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105bb8 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105bb8 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f204 : InstrSpec 0x105bbb [0x31, 0xC1] (fun s => s.RIP = 0x105bbb) (xorR32R32Effect 0x105bbb 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105bbb 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105bbb 0xc1 (by decide)) pre_rip
  have f205 : InstrSpec 0x105bbd [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x105bbd) (andR32Imm32Effect 0x105bbd 6 1 0x2310)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105bbd 6 1 0x2310).toInstrSpec (and_r32_imm32_effect_step 0x105bbd 0xe1 0x2310 (by decide) (by decide)) pre_rip
  have f206 : InstrSpec 0x105bc3 [0x31, 0xC8] (fun s => s.RIP = 0x105bc3) (xorR32R32Effect 0x105bc3 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105bc3 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105bc3 0xc8 (by decide)) pre_rip
  have f207 : InstrSpec 0x105bc5 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105bc5) (shlR32Effect 0x105bc5 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105bc5 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105bc5 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f208 : InstrSpec 0x105bc8 [0x31, 0xC1] (fun s => s.RIP = 0x105bc8) (xorR32R32Effect 0x105bc8 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105bc8 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105bc8 0xc1 (by decide)) pre_rip
  have f209 : InstrSpec 0x105bca [0x89, 0xC8] (fun s => s.RIP = 0x105bca) (movR32R32Effect 0x105bca 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105bca 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105bca 0xc8 (by decide)) pre_rip
  have f210 : InstrSpec 0x105bcc [0xD1, 0xE8] (fun s => s.RIP = 0x105bcc) (shrR32Effect 0x105bcc 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105bcc 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105bcc 0xe8 (by decide) (by decide)) pre_rip
  have f211 : InstrSpec 0x105bce [0x31, 0xC8] (fun s => s.RIP = 0x105bce) (xorR32R32Effect 0x105bce 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105bce 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105bce 0xc8 (by decide)) pre_rip
  have f212 : InstrSpec 0x105bd0 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105bd0) (andEaxImm32Effect 0x105bd0 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105bd0 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105bd0 0x5050) pre_rip
  have f213 : InstrSpec 0x105bd5 [0x31, 0xC1] (fun s => s.RIP = 0x105bd5) (xorR32R32Effect 0x105bd5 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105bd5 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105bd5 0xc1 (by decide)) pre_rip
  have f214 : InstrSpec 0x105bd7 [0x01, 0xC0] (fun s => s.RIP = 0x105bd7) (addR32R32Effect 0x105bd7 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105bd7 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105bd7 0xc0 (by decide)) pre_rip
  have f215 : InstrSpec 0x105bd9 [0x31, 0xC8] (fun s => s.RIP = 0x105bd9) (xorR32R32Effect 0x105bd9 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105bd9 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105bd9 0xc8 (by decide)) pre_rip
  have f216 : InstrSpec 0x105bdb [0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x105bdb 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x105bdb + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105bdb 0 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x105bdb 0 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m32_r32_low_effect_step 0x105bdb 0 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f217 : InstrSpec 0x105be2 [0x0F, 0xB7, 0x44, 0x24, 0x3E] (LoadPre 0x105be2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x105be2 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105be2 5 0 (.sib 4 none 0 (.d8 0x3e)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105be2 5 0 (.sib 4 none 0 (.d8 0x3e))).toInstrSpec (movzx_r32_m16_effect_step 0x105be2 0 (.sib 4 none 0 (.d8 0x3e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f218 : InstrSpec 0x105be7 [0x89, 0xC1] (fun s => s.RIP = 0x105be7) (movR32R32Effect 0x105be7 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105be7 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105be7 0xc1 (by decide)) pre_rip
  have f219 : InstrSpec 0x105be9 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105be9) (shrR32Effect 0x105be9 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105be9 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105be9 0xe9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 437) (RestInside.exec (n := 437) (ρ' := [(0, 431), (1, 435), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bb1) f200 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 438) (RestInside.out (n := 438) f201 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 439) (ρ' := [(0, 438), (1, 435), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bb6) f201 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 440) (RestInside.out (n := 440) f202 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 441) (ρ' := [(0, 438), (1, 440), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bb8) f202 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 442) (RestInside.out (n := 442) f203 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 443) (ρ' := [(0, 438), (1, 442), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bbb) f203 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 444) (RestInside.out (n := 444) f204 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 445) (ρ' := [(0, 438), (1, 444), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bbd) f204 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 446) (RestInside.out (n := 446) f205 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 447) (ρ' := [(0, 438), (1, 446), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bc3) f205 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 448) (RestInside.out (n := 448) f206 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 449) (ρ' := [(0, 448), (1, 446), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bc5) f206 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 450) (RestInside.out (n := 450) f207 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 451) (ρ' := [(0, 448), (1, 450), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bc8) f207 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 452) (RestInside.out (n := 452) f208 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 453) (ρ' := [(0, 448), (1, 452), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bca) f208 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 454) (RestInside.out (n := 454) f209 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 455) (ρ' := [(0, 454), (1, 452), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bcc) f209 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 456) (RestInside.out (n := 456) f210 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 457) (ρ' := [(0, 456), (1, 452), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bce) f210 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 458) (RestInside.out (n := 458) f211 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 459) (ρ' := [(0, 458), (1, 452), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bd0) f211 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 460) (RestInside.out (n := 460) f212 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 461) (ρ' := [(0, 460), (1, 452), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bd5) f212 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 462) (RestInside.out (n := 462) f213 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 463) (ρ' := [(0, 460), (1, 462), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bd7) f213 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 464) (RestInside.out (n := 464) f214 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 465) (ρ' := [(0, 464), (1, 462), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bd9) f214 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 466) (RestInside.out (n := 466) f215 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 467) (ρ' := [(0, 466), (1, 462), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bdb) f215 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 468) (RestInside.exec (n := 468) (ρ' := [(0, 466), (1, 462), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105be2) f216 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 469) (RestInside.out (n := 469) f217 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 470) (ρ' := [(0, 469), (1, 462), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105be7) f217 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 471) (RestInside.out (n := 471) f218 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 472) (ρ' := [(0, 469), (1, 471), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105be9) f218 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 473) (RestInside.out (n := 473) f219 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 474) (ρ' := [(0, 469), (1, 473), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bec) f219 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_11 code

theorem rest_l10593a_9 [Bindings] (code : CodeMap) :
    Rest (n := 399) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 397), (1, 395), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      1012 0x105b67 bytes_l10593a_9 b_l10593a_9 := by
  have f180 : InstrSpec 0x105b67 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105b67) (shlR32Effect 0x105b67 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105b67 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105b67 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f181 : InstrSpec 0x105b6a [0x31, 0xC1] (fun s => s.RIP = 0x105b6a) (xorR32R32Effect 0x105b6a 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105b6a 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105b6a 0xc1 (by decide)) pre_rip
  have f182 : InstrSpec 0x105b6c [0x89, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x105b6c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x105b6c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105b6c 1 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x105b6c 1 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m32_r32_low_effect_step 0x105b6c 1 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f183 : InstrSpec 0x105b73 [0x0F, 0xB7, 0x44, 0x24, 0x38] (LoadPre 0x105b73 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x105b73 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105b73 5 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105b73 5 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (movzx_r32_m16_effect_step 0x105b73 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f184 : InstrSpec 0x105b78 [0x89, 0xC1] (fun s => s.RIP = 0x105b78) (movR32R32Effect 0x105b78 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105b78 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105b78 0xc1 (by decide)) pre_rip
  have f185 : InstrSpec 0x105b7a [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105b7a) (shrR32Effect 0x105b7a 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105b7a 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105b7a 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f186 : InstrSpec 0x105b7d [0x31, 0xC1] (fun s => s.RIP = 0x105b7d) (xorR32R32Effect 0x105b7d 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105b7d 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105b7d 0xc1 (by decide)) pre_rip
  have f187 : InstrSpec 0x105b7f [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105b7f) (andR32Imm32Effect 0x105b7f 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105b7f 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x105b7f 0xe1 0x3030 (by decide) (by decide)) pre_rip
  have f188 : InstrSpec 0x105b85 [0x31, 0xC8] (fun s => s.RIP = 0x105b85) (xorR32R32Effect 0x105b85 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105b85 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105b85 0xc8 (by decide)) pre_rip
  have f189 : InstrSpec 0x105b87 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105b87) (shlR32Effect 0x105b87 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105b87 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105b87 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f190 : InstrSpec 0x105b8a [0x31, 0xC1] (fun s => s.RIP = 0x105b8a) (xorR32R32Effect 0x105b8a 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105b8a 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105b8a 0xc1 (by decide)) pre_rip
  have f191 : InstrSpec 0x105b8c [0x89, 0x8C, 0x24, 0x0C, 0x01, 0x00, 0x00] (StorePre 0x105b8c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10c)) s (0x105b8c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105b8c 1 (.sib 4 none 0 (.d32 0x10c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x105b8c 1 (.sib 4 none 0 (.d32 0x10c))).toInstrSpec (mov_m32_r32_low_effect_step 0x105b8c 1 (.sib 4 none 0 (.d32 0x10c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f192 : InstrSpec 0x105b93 [0x0F, 0xB7, 0x44, 0x24, 0x3A] (LoadPre 0x105b93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x105b93 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105b93 5 0 (.sib 4 none 0 (.d8 0x3a)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105b93 5 0 (.sib 4 none 0 (.d8 0x3a))).toInstrSpec (movzx_r32_m16_effect_step 0x105b93 0 (.sib 4 none 0 (.d8 0x3a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f193 : InstrSpec 0x105b98 [0x89, 0xC1] (fun s => s.RIP = 0x105b98) (movR32R32Effect 0x105b98 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105b98 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105b98 0xc1 (by decide)) pre_rip
  have f194 : InstrSpec 0x105b9a [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105b9a) (shrR32Effect 0x105b9a 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105b9a 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105b9a 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f195 : InstrSpec 0x105b9d [0x31, 0xC1] (fun s => s.RIP = 0x105b9d) (xorR32R32Effect 0x105b9d 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105b9d 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105b9d 0xc1 (by decide)) pre_rip
  have f196 : InstrSpec 0x105b9f [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105b9f) (andR32Imm32Effect 0x105b9f 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105b9f 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x105b9f 0xe1 0x3030 (by decide) (by decide)) pre_rip
  have f197 : InstrSpec 0x105ba5 [0x31, 0xC8] (fun s => s.RIP = 0x105ba5) (xorR32R32Effect 0x105ba5 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105ba5 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105ba5 0xc8 (by decide)) pre_rip
  have f198 : InstrSpec 0x105ba7 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105ba7) (shlR32Effect 0x105ba7 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105ba7 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105ba7 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f199 : InstrSpec 0x105baa [0x31, 0xC1] (fun s => s.RIP = 0x105baa) (xorR32R32Effect 0x105baa 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105baa 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105baa 0xc1 (by decide)) pre_rip
  refine Rest.ofInside (n := 399) (RestInside.out (n := 399) f180 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 400) (ρ' := [(0, 397), (1, 399), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b6a) f180 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 401) (RestInside.out (n := 401) f181 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 402) (ρ' := [(0, 397), (1, 401), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b6c) f181 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 403) (RestInside.exec (n := 403) (ρ' := [(0, 397), (1, 401), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b73) f182 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 404) (RestInside.out (n := 404) f183 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 405) (ρ' := [(0, 404), (1, 401), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b78) f183 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 406) (RestInside.out (n := 406) f184 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 407) (ρ' := [(0, 404), (1, 406), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b7a) f184 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 408) (RestInside.out (n := 408) f185 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 409) (ρ' := [(0, 404), (1, 408), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b7d) f185 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 410) (RestInside.out (n := 410) f186 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 411) (ρ' := [(0, 404), (1, 410), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b7f) f186 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 412) (RestInside.out (n := 412) f187 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 413) (ρ' := [(0, 404), (1, 412), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b85) f187 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 414) (RestInside.out (n := 414) f188 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 415) (ρ' := [(0, 414), (1, 412), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b87) f188 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 416) (RestInside.out (n := 416) f189 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 417) (ρ' := [(0, 414), (1, 416), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b8a) f189 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 418) (RestInside.out (n := 418) f190 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 419) (ρ' := [(0, 414), (1, 418), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b8c) f190 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 420) (RestInside.exec (n := 420) (ρ' := [(0, 414), (1, 418), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b93) f191 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 421) (RestInside.out (n := 421) f192 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 422) (ρ' := [(0, 421), (1, 418), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b98) f192 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 423) (RestInside.out (n := 423) f193 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 424) (ρ' := [(0, 421), (1, 423), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b9a) f193 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 425) (RestInside.out (n := 425) f194 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 426) (ρ' := [(0, 421), (1, 425), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b9d) f194 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 427) (RestInside.out (n := 427) f195 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 428) (ρ' := [(0, 421), (1, 427), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b9f) f195 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 429) (RestInside.out (n := 429) f196 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 430) (ρ' := [(0, 421), (1, 429), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ba5) f196 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 431) (RestInside.out (n := 431) f197 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 432) (ρ' := [(0, 431), (1, 429), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ba7) f197 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 433) (RestInside.out (n := 433) f198 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 434) (ρ' := [(0, 431), (1, 433), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105baa) f198 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 435) (RestInside.out (n := 435) f199 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 436) (ρ' := [(0, 431), (1, 435), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bac) f199 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_10 code

theorem rest_l10593a_8 [Bindings] (code : CodeMap) :
    Rest (n := 361) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 353), (1, 359), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      1032 0x105b23 bytes_l10593a_8 b_l10593a_8 := by
  have f160 : InstrSpec 0x105b23 [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105b23) (andR32Imm32Effect 0x105b23 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105b23 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x105b23 0xe1 0x3030 (by decide) (by decide)) pre_rip
  have f161 : InstrSpec 0x105b29 [0x31, 0xC8] (fun s => s.RIP = 0x105b29) (xorR32R32Effect 0x105b29 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105b29 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105b29 0xc8 (by decide)) pre_rip
  have f162 : InstrSpec 0x105b2b [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105b2b) (shlR32Effect 0x105b2b 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105b2b 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105b2b 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f163 : InstrSpec 0x105b2e [0x31, 0xC1] (fun s => s.RIP = 0x105b2e) (xorR32R32Effect 0x105b2e 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105b2e 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105b2e 0xc1 (by decide)) pre_rip
  have f164 : InstrSpec 0x105b30 [0x66, 0x89, 0x4C, 0x24, 0x32] (StorePre 0x105b30 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x105b30 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105b30 5 1 (.sib 4 none 0 (.d8 0x32)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105b30 5 1 (.sib 4 none 0 (.d8 0x32))).toInstrSpec (mov_m16_r16_effect_step 0x105b30 1 (.sib 4 none 0 (.d8 0x32)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f165 : InstrSpec 0x105b35 [0x0F, 0xB7, 0x44, 0x24, 0x34] (LoadPre 0x105b35 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x105b35 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105b35 5 0 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105b35 5 0 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (movzx_r32_m16_effect_step 0x105b35 0 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f166 : InstrSpec 0x105b3a [0x89, 0xC1] (fun s => s.RIP = 0x105b3a) (movR32R32Effect 0x105b3a 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105b3a 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105b3a 0xc1 (by decide)) pre_rip
  have f167 : InstrSpec 0x105b3c [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105b3c) (shrR32Effect 0x105b3c 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105b3c 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105b3c 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f168 : InstrSpec 0x105b3f [0x31, 0xC1] (fun s => s.RIP = 0x105b3f) (xorR32R32Effect 0x105b3f 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105b3f 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105b3f 0xc1 (by decide)) pre_rip
  have f169 : InstrSpec 0x105b41 [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105b41) (andR32Imm32Effect 0x105b41 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105b41 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x105b41 0xe1 0x3030 (by decide) (by decide)) pre_rip
  have f170 : InstrSpec 0x105b47 [0x31, 0xC8] (fun s => s.RIP = 0x105b47) (xorR32R32Effect 0x105b47 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105b47 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105b47 0xc8 (by decide)) pre_rip
  have f171 : InstrSpec 0x105b49 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105b49) (shlR32Effect 0x105b49 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105b49 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105b49 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f172 : InstrSpec 0x105b4c [0x31, 0xC1] (fun s => s.RIP = 0x105b4c) (xorR32R32Effect 0x105b4c 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105b4c 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105b4c 0xc1 (by decide)) pre_rip
  have f173 : InstrSpec 0x105b4e [0x66, 0x89, 0x4C, 0x24, 0x34] (StorePre 0x105b4e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x105b4e + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105b4e 5 1 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105b4e 5 1 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_m16_r16_effect_step 0x105b4e 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f174 : InstrSpec 0x105b53 [0x0F, 0xB7, 0x44, 0x24, 0x36] (LoadPre 0x105b53 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x105b53 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105b53 5 0 (.sib 4 none 0 (.d8 0x36)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105b53 5 0 (.sib 4 none 0 (.d8 0x36))).toInstrSpec (movzx_r32_m16_effect_step 0x105b53 0 (.sib 4 none 0 (.d8 0x36)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f175 : InstrSpec 0x105b58 [0x89, 0xC1] (fun s => s.RIP = 0x105b58) (movR32R32Effect 0x105b58 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105b58 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105b58 0xc1 (by decide)) pre_rip
  have f176 : InstrSpec 0x105b5a [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105b5a) (shrR32Effect 0x105b5a 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105b5a 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105b5a 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f177 : InstrSpec 0x105b5d [0x31, 0xC1] (fun s => s.RIP = 0x105b5d) (xorR32R32Effect 0x105b5d 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105b5d 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105b5d 0xc1 (by decide)) pre_rip
  have f178 : InstrSpec 0x105b5f [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105b5f) (andR32Imm32Effect 0x105b5f 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105b5f 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x105b5f 0xe1 0x3030 (by decide) (by decide)) pre_rip
  have f179 : InstrSpec 0x105b65 [0x31, 0xC8] (fun s => s.RIP = 0x105b65) (xorR32R32Effect 0x105b65 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105b65 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105b65 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 361) (RestInside.out (n := 361) f160 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 362) (ρ' := [(0, 353), (1, 361), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b29) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 363) (RestInside.out (n := 363) f161 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 364) (ρ' := [(0, 363), (1, 361), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b2b) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 365) (RestInside.out (n := 365) f162 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 366) (ρ' := [(0, 363), (1, 365), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b2e) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 367) (RestInside.out (n := 367) f163 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 368) (ρ' := [(0, 363), (1, 367), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b30) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 369) (RestInside.exec (n := 369) (ρ' := [(0, 363), (1, 367), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b35) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 370) (RestInside.out (n := 370) f165 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 371) (ρ' := [(0, 370), (1, 367), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b3a) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 372) (RestInside.out (n := 372) f166 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 373) (ρ' := [(0, 370), (1, 372), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b3c) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 374) (RestInside.out (n := 374) f167 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 375) (ρ' := [(0, 370), (1, 374), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b3f) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 376) (RestInside.out (n := 376) f168 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 377) (ρ' := [(0, 370), (1, 376), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b41) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 378) (RestInside.out (n := 378) f169 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 379) (ρ' := [(0, 370), (1, 378), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b47) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 380) (RestInside.out (n := 380) f170 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 381) (ρ' := [(0, 380), (1, 378), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b49) f170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 382) (RestInside.out (n := 382) f171 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 383) (ρ' := [(0, 380), (1, 382), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b4c) f171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 384) (RestInside.out (n := 384) f172 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 385) (ρ' := [(0, 380), (1, 384), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b4e) f172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 386) (RestInside.exec (n := 386) (ρ' := [(0, 380), (1, 384), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b53) f173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 387) (RestInside.out (n := 387) f174 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 388) (ρ' := [(0, 387), (1, 384), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b58) f174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 389) (RestInside.out (n := 389) f175 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 390) (ρ' := [(0, 387), (1, 389), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b5a) f175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 391) (RestInside.out (n := 391) f176 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 392) (ρ' := [(0, 387), (1, 391), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b5d) f176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 393) (RestInside.out (n := 393) f177 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 394) (ρ' := [(0, 387), (1, 393), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b5f) f177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 395) (RestInside.out (n := 395) f178 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 396) (ρ' := [(0, 387), (1, 395), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b65) f178 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 397) (RestInside.out (n := 397) f179 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 398) (ρ' := [(0, 397), (1, 395), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b67) f179 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_9 code

theorem rest_l10593a_7 [Bindings] (code : CodeMap) :
    Rest (n := 323) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 319), (1, 321), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      1052 0x105ae0 bytes_l10593a_7 b_l10593a_7 := by
  have f140 : InstrSpec 0x105ae0 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105ae0) (shrR32Effect 0x105ae0 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105ae0 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105ae0 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f141 : InstrSpec 0x105ae3 [0x31, 0xC1] (fun s => s.RIP = 0x105ae3) (xorR32R32Effect 0x105ae3 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105ae3 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105ae3 0xc1 (by decide)) pre_rip
  have f142 : InstrSpec 0x105ae5 [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105ae5) (andR32Imm32Effect 0x105ae5 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105ae5 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x105ae5 0xe1 0x3030 (by decide) (by decide)) pre_rip
  have f143 : InstrSpec 0x105aeb [0x31, 0xC8] (fun s => s.RIP = 0x105aeb) (xorR32R32Effect 0x105aeb 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105aeb 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105aeb 0xc8 (by decide)) pre_rip
  have f144 : InstrSpec 0x105aed [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105aed) (shlR32Effect 0x105aed 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105aed 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105aed 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f145 : InstrSpec 0x105af0 [0x31, 0xC1] (fun s => s.RIP = 0x105af0) (xorR32R32Effect 0x105af0 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105af0 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105af0 0xc1 (by decide)) pre_rip
  have f146 : InstrSpec 0x105af2 [0x89, 0x8C, 0x24, 0x14, 0x01, 0x00, 0x00] (StorePre 0x105af2 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x114)) s (0x105af2 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105af2 1 (.sib 4 none 0 (.d32 0x114)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x105af2 1 (.sib 4 none 0 (.d32 0x114))).toInstrSpec (mov_m32_r32_low_effect_step 0x105af2 1 (.sib 4 none 0 (.d32 0x114)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f147 : InstrSpec 0x105af9 [0x0F, 0xB7, 0x44, 0x24, 0x30] (LoadPre 0x105af9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x105af9 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105af9 5 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105af9 5 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (movzx_r32_m16_effect_step 0x105af9 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f148 : InstrSpec 0x105afe [0x89, 0xC1] (fun s => s.RIP = 0x105afe) (movR32R32Effect 0x105afe 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105afe 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105afe 0xc1 (by decide)) pre_rip
  have f149 : InstrSpec 0x105b00 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105b00) (shrR32Effect 0x105b00 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105b00 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105b00 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f150 : InstrSpec 0x105b03 [0x31, 0xC1] (fun s => s.RIP = 0x105b03) (xorR32R32Effect 0x105b03 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105b03 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105b03 0xc1 (by decide)) pre_rip
  have f151 : InstrSpec 0x105b05 [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105b05) (andR32Imm32Effect 0x105b05 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105b05 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x105b05 0xe1 0x3030 (by decide) (by decide)) pre_rip
  have f152 : InstrSpec 0x105b0b [0x31, 0xC8] (fun s => s.RIP = 0x105b0b) (xorR32R32Effect 0x105b0b 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105b0b 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105b0b 0xc8 (by decide)) pre_rip
  have f153 : InstrSpec 0x105b0d [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105b0d) (shlR32Effect 0x105b0d 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105b0d 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105b0d 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f154 : InstrSpec 0x105b10 [0x31, 0xC1] (fun s => s.RIP = 0x105b10) (xorR32R32Effect 0x105b10 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105b10 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105b10 0xc1 (by decide)) pre_rip
  have f155 : InstrSpec 0x105b12 [0x66, 0x89, 0x4C, 0x24, 0x30] (StorePre 0x105b12 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x105b12 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105b12 5 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105b12 5 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m16_r16_effect_step 0x105b12 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f156 : InstrSpec 0x105b17 [0x0F, 0xB7, 0x44, 0x24, 0x32] (LoadPre 0x105b17 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x105b17 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105b17 5 0 (.sib 4 none 0 (.d8 0x32)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105b17 5 0 (.sib 4 none 0 (.d8 0x32))).toInstrSpec (movzx_r32_m16_effect_step 0x105b17 0 (.sib 4 none 0 (.d8 0x32)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f157 : InstrSpec 0x105b1c [0x89, 0xC1] (fun s => s.RIP = 0x105b1c) (movR32R32Effect 0x105b1c 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105b1c 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105b1c 0xc1 (by decide)) pre_rip
  have f158 : InstrSpec 0x105b1e [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105b1e) (shrR32Effect 0x105b1e 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105b1e 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105b1e 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f159 : InstrSpec 0x105b21 [0x31, 0xC1] (fun s => s.RIP = 0x105b21) (xorR32R32Effect 0x105b21 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105b21 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105b21 0xc1 (by decide)) pre_rip
  refine Rest.ofInside (n := 323) (RestInside.out (n := 323) f140 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 324) (ρ' := [(0, 319), (1, 323), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ae3) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 325) (RestInside.out (n := 325) f141 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 326) (ρ' := [(0, 319), (1, 325), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ae5) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 327) (RestInside.out (n := 327) f142 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 328) (ρ' := [(0, 319), (1, 327), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105aeb) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 329) (RestInside.out (n := 329) f143 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 330) (ρ' := [(0, 329), (1, 327), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105aed) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 331) (RestInside.out (n := 331) f144 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 332) (ρ' := [(0, 329), (1, 331), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105af0) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 333) (RestInside.out (n := 333) f145 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 334) (ρ' := [(0, 329), (1, 333), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105af2) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 335) (RestInside.exec (n := 335) (ρ' := [(0, 329), (1, 333), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105af9) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 336) (RestInside.out (n := 336) f147 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 337) (ρ' := [(0, 336), (1, 333), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105afe) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 338) (RestInside.out (n := 338) f148 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 339) (ρ' := [(0, 336), (1, 338), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b00) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 340) (RestInside.out (n := 340) f149 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 341) (ρ' := [(0, 336), (1, 340), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b03) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 342) (RestInside.out (n := 342) f150 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 343) (ρ' := [(0, 336), (1, 342), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b05) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 344) (RestInside.out (n := 344) f151 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 345) (ρ' := [(0, 336), (1, 344), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b0b) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 346) (RestInside.out (n := 346) f152 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 347) (ρ' := [(0, 346), (1, 344), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b0d) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 348) (RestInside.out (n := 348) f153 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 349) (ρ' := [(0, 346), (1, 348), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b10) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 350) (RestInside.out (n := 350) f154 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 351) (ρ' := [(0, 346), (1, 350), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b12) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 352) (RestInside.exec (n := 352) (ρ' := [(0, 346), (1, 350), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b17) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 353) (RestInside.out (n := 353) f156 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 354) (ρ' := [(0, 353), (1, 350), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b1c) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 355) (RestInside.out (n := 355) f157 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 356) (ρ' := [(0, 353), (1, 355), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b1e) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 357) (RestInside.out (n := 357) f158 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 358) (ρ' := [(0, 353), (1, 357), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b21) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 359) (RestInside.out (n := 359) f159 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 360) (ρ' := [(0, 353), (1, 359), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b23) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_8 code

theorem rest_l10593a_6 [Bindings] (code : CodeMap) :
    Rest (n := 285) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 281), (1, 283), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      1072 0x105aa1 bytes_l10593a_6 b_l10593a_6 := by
  have f120 : InstrSpec 0x105aa1 [0x31, 0xC1] (fun s => s.RIP = 0x105aa1) (xorR32R32Effect 0x105aa1 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105aa1 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105aa1 0xc1 (by decide)) pre_rip
  have f121 : InstrSpec 0x105aa3 [0x89, 0xC8] (fun s => s.RIP = 0x105aa3) (movR32R32Effect 0x105aa3 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105aa3 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105aa3 0xc8 (by decide)) pre_rip
  have f122 : InstrSpec 0x105aa5 [0xD1, 0xE8] (fun s => s.RIP = 0x105aa5) (shrR32Effect 0x105aa5 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105aa5 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105aa5 0xe8 (by decide) (by decide)) pre_rip
  have f123 : InstrSpec 0x105aa7 [0x31, 0xC8] (fun s => s.RIP = 0x105aa7) (xorR32R32Effect 0x105aa7 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105aa7 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105aa7 0xc8 (by decide)) pre_rip
  have f124 : InstrSpec 0x105aa9 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105aa9) (andEaxImm32Effect 0x105aa9 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105aa9 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105aa9 0x5050) pre_rip
  have f125 : InstrSpec 0x105aae [0x31, 0xC1] (fun s => s.RIP = 0x105aae) (xorR32R32Effect 0x105aae 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105aae 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105aae 0xc1 (by decide)) pre_rip
  have f126 : InstrSpec 0x105ab0 [0x01, 0xC0] (fun s => s.RIP = 0x105ab0) (addR32R32Effect 0x105ab0 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105ab0 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105ab0 0xc0 (by decide)) pre_rip
  have f127 : InstrSpec 0x105ab2 [0x31, 0xC8] (fun s => s.RIP = 0x105ab2) (xorR32R32Effect 0x105ab2 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105ab2 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105ab2 0xc8 (by decide)) pre_rip
  have f128 : InstrSpec 0x105ab4 [0x66, 0x89, 0x44, 0x24, 0x2A] (StorePre 0x105ab4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x105ab4 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105ab4 5 0 (.sib 4 none 0 (.d8 0x2a)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105ab4 5 0 (.sib 4 none 0 (.d8 0x2a))).toInstrSpec (mov_m16_r16_effect_step 0x105ab4 0 (.sib 4 none 0 (.d8 0x2a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f129 : InstrSpec 0x105ab9 [0x0F, 0xB7, 0x44, 0x24, 0x2C] (LoadPre 0x105ab9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x105ab9 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105ab9 5 0 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105ab9 5 0 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (movzx_r32_m16_effect_step 0x105ab9 0 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f130 : InstrSpec 0x105abe [0x89, 0xC1] (fun s => s.RIP = 0x105abe) (movR32R32Effect 0x105abe 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105abe 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105abe 0xc1 (by decide)) pre_rip
  have f131 : InstrSpec 0x105ac0 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105ac0) (shrR32Effect 0x105ac0 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105ac0 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105ac0 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f132 : InstrSpec 0x105ac3 [0x31, 0xC1] (fun s => s.RIP = 0x105ac3) (xorR32R32Effect 0x105ac3 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105ac3 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105ac3 0xc1 (by decide)) pre_rip
  have f133 : InstrSpec 0x105ac5 [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105ac5) (andR32Imm32Effect 0x105ac5 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105ac5 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x105ac5 0xe1 0x3030 (by decide) (by decide)) pre_rip
  have f134 : InstrSpec 0x105acb [0x31, 0xC8] (fun s => s.RIP = 0x105acb) (xorR32R32Effect 0x105acb 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105acb 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105acb 0xc8 (by decide)) pre_rip
  have f135 : InstrSpec 0x105acd [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105acd) (shlR32Effect 0x105acd 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105acd 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105acd 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f136 : InstrSpec 0x105ad0 [0x31, 0xC1] (fun s => s.RIP = 0x105ad0) (xorR32R32Effect 0x105ad0 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105ad0 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105ad0 0xc1 (by decide)) pre_rip
  have f137 : InstrSpec 0x105ad2 [0x89, 0x8C, 0x24, 0x18, 0x01, 0x00, 0x00] (StorePre 0x105ad2 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x105ad2 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105ad2 1 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x105ad2 1 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_m32_r32_low_effect_step 0x105ad2 1 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f138 : InstrSpec 0x105ad9 [0x0F, 0xB7, 0x44, 0x24, 0x2E] (LoadPre 0x105ad9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2e)) s (0x105ad9 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105ad9 5 0 (.sib 4 none 0 (.d8 0x2e)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105ad9 5 0 (.sib 4 none 0 (.d8 0x2e))).toInstrSpec (movzx_r32_m16_effect_step 0x105ad9 0 (.sib 4 none 0 (.d8 0x2e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f139 : InstrSpec 0x105ade [0x89, 0xC1] (fun s => s.RIP = 0x105ade) (movR32R32Effect 0x105ade 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105ade 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105ade 0xc1 (by decide)) pre_rip
  refine Rest.ofInside (n := 285) (RestInside.out (n := 285) f120 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 286) (ρ' := [(0, 281), (1, 285), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105aa3) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 287) (RestInside.out (n := 287) f121 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 288) (ρ' := [(0, 287), (1, 285), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105aa5) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 289) (RestInside.out (n := 289) f122 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 290) (ρ' := [(0, 289), (1, 285), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105aa7) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 291) (RestInside.out (n := 291) f123 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 292) (ρ' := [(0, 291), (1, 285), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105aa9) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 293) (RestInside.out (n := 293) f124 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 294) (ρ' := [(0, 293), (1, 285), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105aae) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 295) (RestInside.out (n := 295) f125 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 296) (ρ' := [(0, 293), (1, 295), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ab0) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 297) (RestInside.out (n := 297) f126 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 298) (ρ' := [(0, 297), (1, 295), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ab2) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 299) (RestInside.out (n := 299) f127 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 300) (ρ' := [(0, 299), (1, 295), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ab4) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 301) (RestInside.exec (n := 301) (ρ' := [(0, 299), (1, 295), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ab9) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f129 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 303) (ρ' := [(0, 302), (1, 295), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105abe) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f130 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 305) (ρ' := [(0, 302), (1, 304), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ac0) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 306) (RestInside.out (n := 306) f131 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 307) (ρ' := [(0, 302), (1, 306), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ac3) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 308) (RestInside.out (n := 308) f132 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 309) (ρ' := [(0, 302), (1, 308), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ac5) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 310) (RestInside.out (n := 310) f133 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 311) (ρ' := [(0, 302), (1, 310), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105acb) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 312) (RestInside.out (n := 312) f134 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 313) (ρ' := [(0, 312), (1, 310), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105acd) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 314) (RestInside.out (n := 314) f135 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 315) (ρ' := [(0, 312), (1, 314), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ad0) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 316) (RestInside.out (n := 316) f136 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 317) (ρ' := [(0, 312), (1, 316), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ad2) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 318) (RestInside.exec (n := 318) (ρ' := [(0, 312), (1, 316), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ad9) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 319) (RestInside.out (n := 319) f138 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 320) (ρ' := [(0, 319), (1, 316), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ade) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 321) (RestInside.out (n := 321) f139 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 322) (ρ' := [(0, 319), (1, 321), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ae0) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_7 code

theorem rest_l10593a_5 [Bindings] (code : CodeMap) :
    Rest (n := 246) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 240), (1, 244), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      1092 0x105a65 bytes_l10593a_5 b_l10593a_5 := by
  have f100 : InstrSpec 0x105a65 [0x31, 0xC1] (fun s => s.RIP = 0x105a65) (xorR32R32Effect 0x105a65 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a65 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105a65 0xc1 (by decide)) pre_rip
  have f101 : InstrSpec 0x105a67 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x105a67) (andR32Imm32Effect 0x105a67 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105a67 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x105a67 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x105a6d [0x31, 0xC8] (fun s => s.RIP = 0x105a6d) (xorR32R32Effect 0x105a6d 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a6d 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105a6d 0xc8 (by decide)) pre_rip
  have f103 : InstrSpec 0x105a6f [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105a6f) (shlR32Effect 0x105a6f 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105a6f 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105a6f 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f104 : InstrSpec 0x105a72 [0x31, 0xC1] (fun s => s.RIP = 0x105a72) (xorR32R32Effect 0x105a72 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a72 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105a72 0xc1 (by decide)) pre_rip
  have f105 : InstrSpec 0x105a74 [0x89, 0xC8] (fun s => s.RIP = 0x105a74) (movR32R32Effect 0x105a74 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105a74 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105a74 0xc8 (by decide)) pre_rip
  have f106 : InstrSpec 0x105a76 [0xD1, 0xE8] (fun s => s.RIP = 0x105a76) (shrR32Effect 0x105a76 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105a76 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105a76 0xe8 (by decide) (by decide)) pre_rip
  have f107 : InstrSpec 0x105a78 [0x31, 0xC8] (fun s => s.RIP = 0x105a78) (xorR32R32Effect 0x105a78 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a78 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105a78 0xc8 (by decide)) pre_rip
  have f108 : InstrSpec 0x105a7a [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105a7a) (andEaxImm32Effect 0x105a7a 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105a7a 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105a7a 0x5050) pre_rip
  have f109 : InstrSpec 0x105a7f [0x31, 0xC1] (fun s => s.RIP = 0x105a7f) (xorR32R32Effect 0x105a7f 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a7f 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105a7f 0xc1 (by decide)) pre_rip
  have f110 : InstrSpec 0x105a81 [0x01, 0xC0] (fun s => s.RIP = 0x105a81) (addR32R32Effect 0x105a81 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105a81 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105a81 0xc0 (by decide)) pre_rip
  have f111 : InstrSpec 0x105a83 [0x31, 0xC8] (fun s => s.RIP = 0x105a83) (xorR32R32Effect 0x105a83 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a83 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105a83 0xc8 (by decide)) pre_rip
  have f112 : InstrSpec 0x105a85 [0x66, 0x89, 0x44, 0x24, 0x28] (StorePre 0x105a85 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105a85 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105a85 5 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105a85 5 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m16_r16_effect_step 0x105a85 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f113 : InstrSpec 0x105a8a [0x0F, 0xB7, 0x44, 0x24, 0x2A] (LoadPre 0x105a8a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x105a8a + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105a8a 5 0 (.sib 4 none 0 (.d8 0x2a)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105a8a 5 0 (.sib 4 none 0 (.d8 0x2a))).toInstrSpec (movzx_r32_m16_effect_step 0x105a8a 0 (.sib 4 none 0 (.d8 0x2a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f114 : InstrSpec 0x105a8f [0x89, 0xC1] (fun s => s.RIP = 0x105a8f) (movR32R32Effect 0x105a8f 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105a8f 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105a8f 0xc1 (by decide)) pre_rip
  have f115 : InstrSpec 0x105a91 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105a91) (shrR32Effect 0x105a91 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105a91 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105a91 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f116 : InstrSpec 0x105a94 [0x31, 0xC1] (fun s => s.RIP = 0x105a94) (xorR32R32Effect 0x105a94 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a94 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105a94 0xc1 (by decide)) pre_rip
  have f117 : InstrSpec 0x105a96 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x105a96) (andR32Imm32Effect 0x105a96 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105a96 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x105a96 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x105a9c [0x31, 0xC8] (fun s => s.RIP = 0x105a9c) (xorR32R32Effect 0x105a9c 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a9c 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105a9c 0xc8 (by decide)) pre_rip
  have f119 : InstrSpec 0x105a9e [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105a9e) (shlR32Effect 0x105a9e 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105a9e 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105a9e 0xe1 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 246) (RestInside.out (n := 246) f100 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 247) (ρ' := [(0, 240), (1, 246), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a67) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 248) (RestInside.out (n := 248) f101 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 249) (ρ' := [(0, 240), (1, 248), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a6d) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 250) (RestInside.out (n := 250) f102 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 251) (ρ' := [(0, 250), (1, 248), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a6f) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 252) (RestInside.out (n := 252) f103 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 253) (ρ' := [(0, 250), (1, 252), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a72) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 254) (RestInside.out (n := 254) f104 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 255) (ρ' := [(0, 250), (1, 254), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a74) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 256) (RestInside.out (n := 256) f105 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 257) (ρ' := [(0, 256), (1, 254), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a76) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 258) (RestInside.out (n := 258) f106 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 259) (ρ' := [(0, 258), (1, 254), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a78) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 260) (RestInside.out (n := 260) f107 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 261) (ρ' := [(0, 260), (1, 254), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a7a) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 262) (RestInside.out (n := 262) f108 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 263) (ρ' := [(0, 262), (1, 254), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a7f) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 264) (RestInside.out (n := 264) f109 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 265) (ρ' := [(0, 262), (1, 264), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a81) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 266) (RestInside.out (n := 266) f110 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 267) (ρ' := [(0, 266), (1, 264), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a83) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f111 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 269) (ρ' := [(0, 268), (1, 264), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a85) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 270) (RestInside.exec (n := 270) (ρ' := [(0, 268), (1, 264), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a8a) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 271) (RestInside.out (n := 271) f113 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 272) (ρ' := [(0, 271), (1, 264), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a8f) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 273) (RestInside.out (n := 273) f114 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 274) (ρ' := [(0, 271), (1, 273), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a91) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 275) (RestInside.out (n := 275) f115 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 276) (ρ' := [(0, 271), (1, 275), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a94) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 277) (RestInside.out (n := 277) f116 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 278) (ρ' := [(0, 271), (1, 277), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a96) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 279) (RestInside.out (n := 279) f117 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 280) (ρ' := [(0, 271), (1, 279), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a9c) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 281) (RestInside.out (n := 281) f118 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 282) (ρ' := [(0, 281), (1, 279), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a9e) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 283) (RestInside.out (n := 283) f119 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 284) (ρ' := [(0, 281), (1, 283), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105aa1) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_6 code

theorem rest_l10593a_4 [Bindings] (code : CodeMap) :
    Rest (n := 208) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 206), (1, 202), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      1112 0x105a27 bytes_l10593a_4 b_l10593a_4 := by
  have f80 : InstrSpec 0x105a27 [0x66, 0x89, 0x44, 0x24, 0x24] (StorePre 0x105a27 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x105a27 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105a27 5 0 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105a27 5 0 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_m16_r16_effect_step 0x105a27 0 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f81 : InstrSpec 0x105a2c [0x0F, 0xB7, 0x44, 0x24, 0x26] (LoadPre 0x105a2c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x105a2c + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105a2c 5 0 (.sib 4 none 0 (.d8 0x26)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105a2c 5 0 (.sib 4 none 0 (.d8 0x26))).toInstrSpec (movzx_r32_m16_effect_step 0x105a2c 0 (.sib 4 none 0 (.d8 0x26)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f82 : InstrSpec 0x105a31 [0x89, 0xC1] (fun s => s.RIP = 0x105a31) (movR32R32Effect 0x105a31 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105a31 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105a31 0xc1 (by decide)) pre_rip
  have f83 : InstrSpec 0x105a33 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105a33) (shrR32Effect 0x105a33 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105a33 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105a33 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x105a36 [0x31, 0xC1] (fun s => s.RIP = 0x105a36) (xorR32R32Effect 0x105a36 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a36 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105a36 0xc1 (by decide)) pre_rip
  have f85 : InstrSpec 0x105a38 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x105a38) (andR32Imm32Effect 0x105a38 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105a38 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x105a38 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x105a3e [0x31, 0xC8] (fun s => s.RIP = 0x105a3e) (xorR32R32Effect 0x105a3e 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a3e 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105a3e 0xc8 (by decide)) pre_rip
  have f87 : InstrSpec 0x105a40 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105a40) (shlR32Effect 0x105a40 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105a40 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105a40 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x105a43 [0x31, 0xC1] (fun s => s.RIP = 0x105a43) (xorR32R32Effect 0x105a43 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a43 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105a43 0xc1 (by decide)) pre_rip
  have f89 : InstrSpec 0x105a45 [0x89, 0xC8] (fun s => s.RIP = 0x105a45) (movR32R32Effect 0x105a45 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105a45 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105a45 0xc8 (by decide)) pre_rip
  have f90 : InstrSpec 0x105a47 [0xD1, 0xE8] (fun s => s.RIP = 0x105a47) (shrR32Effect 0x105a47 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105a47 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105a47 0xe8 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x105a49 [0x31, 0xC8] (fun s => s.RIP = 0x105a49) (xorR32R32Effect 0x105a49 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a49 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105a49 0xc8 (by decide)) pre_rip
  have f92 : InstrSpec 0x105a4b [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105a4b) (andEaxImm32Effect 0x105a4b 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105a4b 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105a4b 0x5050) pre_rip
  have f93 : InstrSpec 0x105a50 [0x31, 0xC1] (fun s => s.RIP = 0x105a50) (xorR32R32Effect 0x105a50 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a50 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105a50 0xc1 (by decide)) pre_rip
  have f94 : InstrSpec 0x105a52 [0x01, 0xC0] (fun s => s.RIP = 0x105a52) (addR32R32Effect 0x105a52 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105a52 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105a52 0xc0 (by decide)) pre_rip
  have f95 : InstrSpec 0x105a54 [0x31, 0xC8] (fun s => s.RIP = 0x105a54) (xorR32R32Effect 0x105a54 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a54 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105a54 0xc8 (by decide)) pre_rip
  have f96 : InstrSpec 0x105a56 [0x66, 0x89, 0x44, 0x24, 0x26] (StorePre 0x105a56 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x105a56 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105a56 5 0 (.sib 4 none 0 (.d8 0x26)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105a56 5 0 (.sib 4 none 0 (.d8 0x26))).toInstrSpec (mov_m16_r16_effect_step 0x105a56 0 (.sib 4 none 0 (.d8 0x26)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f97 : InstrSpec 0x105a5b [0x0F, 0xB7, 0x44, 0x24, 0x28] (LoadPre 0x105a5b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105a5b + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105a5b 5 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105a5b 5 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (movzx_r32_m16_effect_step 0x105a5b 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f98 : InstrSpec 0x105a60 [0x89, 0xC1] (fun s => s.RIP = 0x105a60) (movR32R32Effect 0x105a60 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105a60 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105a60 0xc1 (by decide)) pre_rip
  have f99 : InstrSpec 0x105a62 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105a62) (shrR32Effect 0x105a62 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105a62 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105a62 0xe9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 208) (RestInside.exec (n := 208) (ρ' := [(0, 206), (1, 202), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a2c) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 209) (RestInside.out (n := 209) f81 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 210) (ρ' := [(0, 209), (1, 202), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a31) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 211) (RestInside.out (n := 211) f82 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 212) (ρ' := [(0, 209), (1, 211), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a33) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 213) (RestInside.out (n := 213) f83 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 214) (ρ' := [(0, 209), (1, 213), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a36) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 215) (RestInside.out (n := 215) f84 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 216) (ρ' := [(0, 209), (1, 215), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a38) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 217) (RestInside.out (n := 217) f85 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 218) (ρ' := [(0, 209), (1, 217), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a3e) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f86 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 219), (1, 217), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a40) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f87 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 219), (1, 221), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a43) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f88 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(0, 219), (1, 223), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a45) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f89 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(0, 225), (1, 223), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a47) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f90 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 227), (1, 223), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a49) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.out (n := 229) f91 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 230) (ρ' := [(0, 229), (1, 223), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a4b) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.out (n := 231) f92 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 232) (ρ' := [(0, 231), (1, 223), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a50) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 233) (RestInside.out (n := 233) f93 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 234) (ρ' := [(0, 231), (1, 233), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a52) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 235) (RestInside.out (n := 235) f94 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 236) (ρ' := [(0, 235), (1, 233), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a54) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 237) (RestInside.out (n := 237) f95 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 238) (ρ' := [(0, 237), (1, 233), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a56) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 239) (RestInside.exec (n := 239) (ρ' := [(0, 237), (1, 233), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a5b) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f97 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 241) (ρ' := [(0, 240), (1, 233), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a60) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 242) (RestInside.out (n := 242) f98 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 243) (ρ' := [(0, 240), (1, 242), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a62) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 244) (RestInside.out (n := 244) f99 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 245) (ρ' := [(0, 240), (1, 244), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a65) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_5 code

theorem rest_l10593a_3 [Bindings] (code : CodeMap) :
    Rest (n := 169) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 167), (1, 161), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      1132 0x1059ed bytes_l10593a_3 b_l10593a_3 := by
  have f60 : InstrSpec 0x1059ed [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1059ed) (andEaxImm32Effect 0x1059ed 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x1059ed 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x1059ed 0x5050) pre_rip
  have f61 : InstrSpec 0x1059f2 [0x31, 0xC1] (fun s => s.RIP = 0x1059f2) (xorR32R32Effect 0x1059f2 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1059f2 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1059f2 0xc1 (by decide)) pre_rip
  have f62 : InstrSpec 0x1059f4 [0x01, 0xC0] (fun s => s.RIP = 0x1059f4) (addR32R32Effect 0x1059f4 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1059f4 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x1059f4 0xc0 (by decide)) pre_rip
  have f63 : InstrSpec 0x1059f6 [0x31, 0xC8] (fun s => s.RIP = 0x1059f6) (xorR32R32Effect 0x1059f6 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1059f6 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1059f6 0xc8 (by decide)) pre_rip
  have f64 : InstrSpec 0x1059f8 [0x66, 0x89, 0x44, 0x24, 0x22] (StorePre 0x1059f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x1059f8 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1059f8 5 0 (.sib 4 none 0 (.d8 0x22)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1059f8 5 0 (.sib 4 none 0 (.d8 0x22))).toInstrSpec (mov_m16_r16_effect_step 0x1059f8 0 (.sib 4 none 0 (.d8 0x22)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f65 : InstrSpec 0x1059fd [0x0F, 0xB7, 0x44, 0x24, 0x24] (LoadPre 0x1059fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1059fd + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1059fd 5 0 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1059fd 5 0 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (movzx_r32_m16_effect_step 0x1059fd 0 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f66 : InstrSpec 0x105a02 [0x89, 0xC1] (fun s => s.RIP = 0x105a02) (movR32R32Effect 0x105a02 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105a02 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105a02 0xc1 (by decide)) pre_rip
  have f67 : InstrSpec 0x105a04 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105a04) (shrR32Effect 0x105a04 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105a04 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105a04 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x105a07 [0x31, 0xC1] (fun s => s.RIP = 0x105a07) (xorR32R32Effect 0x105a07 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a07 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105a07 0xc1 (by decide)) pre_rip
  have f69 : InstrSpec 0x105a09 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x105a09) (andR32Imm32Effect 0x105a09 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105a09 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x105a09 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x105a0f [0x31, 0xC8] (fun s => s.RIP = 0x105a0f) (xorR32R32Effect 0x105a0f 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a0f 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105a0f 0xc8 (by decide)) pre_rip
  have f71 : InstrSpec 0x105a11 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105a11) (shlR32Effect 0x105a11 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105a11 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105a11 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x105a14 [0x31, 0xC1] (fun s => s.RIP = 0x105a14) (xorR32R32Effect 0x105a14 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a14 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105a14 0xc1 (by decide)) pre_rip
  have f73 : InstrSpec 0x105a16 [0x89, 0xC8] (fun s => s.RIP = 0x105a16) (movR32R32Effect 0x105a16 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105a16 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105a16 0xc8 (by decide)) pre_rip
  have f74 : InstrSpec 0x105a18 [0xD1, 0xE8] (fun s => s.RIP = 0x105a18) (shrR32Effect 0x105a18 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105a18 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105a18 0xe8 (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x105a1a [0x31, 0xC8] (fun s => s.RIP = 0x105a1a) (xorR32R32Effect 0x105a1a 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a1a 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105a1a 0xc8 (by decide)) pre_rip
  have f76 : InstrSpec 0x105a1c [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105a1c) (andEaxImm32Effect 0x105a1c 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105a1c 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105a1c 0x5050) pre_rip
  have f77 : InstrSpec 0x105a21 [0x31, 0xC1] (fun s => s.RIP = 0x105a21) (xorR32R32Effect 0x105a21 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a21 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105a21 0xc1 (by decide)) pre_rip
  have f78 : InstrSpec 0x105a23 [0x01, 0xC0] (fun s => s.RIP = 0x105a23) (addR32R32Effect 0x105a23 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105a23 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105a23 0xc0 (by decide)) pre_rip
  have f79 : InstrSpec 0x105a25 [0x31, 0xC8] (fun s => s.RIP = 0x105a25) (xorR32R32Effect 0x105a25 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105a25 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105a25 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f60 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 169), (1, 161), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059f2) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f61 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 169), (1, 171), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059f4) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f62 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 173), (1, 171), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059f6) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f63 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 175), (1, 171), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059f8) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.exec (n := 177) (ρ' := [(0, 175), (1, 171), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059fd) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 178) (RestInside.out (n := 178) f65 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 179) (ρ' := [(0, 178), (1, 171), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a02) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f66 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(0, 178), (1, 180), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a04) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f67 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 178), (1, 182), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a07) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f68 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(0, 178), (1, 184), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a09) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 186) (RestInside.out (n := 186) f69 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 187) (ρ' := [(0, 178), (1, 186), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a0f) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 188) (RestInside.out (n := 188) f70 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 189) (ρ' := [(0, 188), (1, 186), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a11) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 190) (RestInside.out (n := 190) f71 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 191) (ρ' := [(0, 188), (1, 190), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a14) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 192) (RestInside.out (n := 192) f72 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 193) (ρ' := [(0, 188), (1, 192), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a16) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 194) (RestInside.out (n := 194) f73 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 195) (ρ' := [(0, 194), (1, 192), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a18) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 196) (RestInside.out (n := 196) f74 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 197) (ρ' := [(0, 196), (1, 192), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a1a) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 198) (RestInside.out (n := 198) f75 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 199) (ρ' := [(0, 198), (1, 192), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a1c) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f76 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 200), (1, 192), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a21) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f77 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 200), (1, 202), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a23) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f78 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 204), (1, 202), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a25) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f79 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 206), (1, 202), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a27) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_4 code

theorem rest_l10593a_2 [Bindings] (code : CodeMap) :
    Rest (n := 130) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 126), (1, 128), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      1152 0x1059b6 bytes_l10593a_2 b_l10593a_2 := by
  have f40 : InstrSpec 0x1059b6 [0x31, 0xC1] (fun s => s.RIP = 0x1059b6) (xorR32R32Effect 0x1059b6 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1059b6 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1059b6 0xc1 (by decide)) pre_rip
  have f41 : InstrSpec 0x1059b8 [0x89, 0xC8] (fun s => s.RIP = 0x1059b8) (movR32R32Effect 0x1059b8 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1059b8 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x1059b8 0xc8 (by decide)) pre_rip
  have f42 : InstrSpec 0x1059ba [0xD1, 0xE8] (fun s => s.RIP = 0x1059ba) (shrR32Effect 0x1059ba 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x1059ba 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x1059ba 0xe8 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x1059bc [0x31, 0xC8] (fun s => s.RIP = 0x1059bc) (xorR32R32Effect 0x1059bc 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1059bc 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1059bc 0xc8 (by decide)) pre_rip
  have f44 : InstrSpec 0x1059be [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1059be) (andEaxImm32Effect 0x1059be 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x1059be 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x1059be 0x5050) pre_rip
  have f45 : InstrSpec 0x1059c3 [0x31, 0xC1] (fun s => s.RIP = 0x1059c3) (xorR32R32Effect 0x1059c3 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1059c3 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1059c3 0xc1 (by decide)) pre_rip
  have f46 : InstrSpec 0x1059c5 [0x01, 0xC0] (fun s => s.RIP = 0x1059c5) (addR32R32Effect 0x1059c5 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1059c5 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x1059c5 0xc0 (by decide)) pre_rip
  have f47 : InstrSpec 0x1059c7 [0x31, 0xC8] (fun s => s.RIP = 0x1059c7) (xorR32R32Effect 0x1059c7 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1059c7 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1059c7 0xc8 (by decide)) pre_rip
  have f48 : InstrSpec 0x1059c9 [0x66, 0x89, 0x44, 0x24, 0x20] (StorePre 0x1059c9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1059c9 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1059c9 5 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1059c9 5 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m16_r16_effect_step 0x1059c9 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x1059ce [0x0F, 0xB7, 0x44, 0x24, 0x22] (LoadPre 0x1059ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x1059ce + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1059ce 5 0 (.sib 4 none 0 (.d8 0x22)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1059ce 5 0 (.sib 4 none 0 (.d8 0x22))).toInstrSpec (movzx_r32_m16_effect_step 0x1059ce 0 (.sib 4 none 0 (.d8 0x22)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f50 : InstrSpec 0x1059d3 [0x89, 0xC1] (fun s => s.RIP = 0x1059d3) (movR32R32Effect 0x1059d3 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1059d3 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1059d3 0xc1 (by decide)) pre_rip
  have f51 : InstrSpec 0x1059d5 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x1059d5) (shrR32Effect 0x1059d5 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1059d5 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x1059d5 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x1059d8 [0x31, 0xC1] (fun s => s.RIP = 0x1059d8) (xorR32R32Effect 0x1059d8 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1059d8 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1059d8 0xc1 (by decide)) pre_rip
  have f53 : InstrSpec 0x1059da [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x1059da) (andR32Imm32Effect 0x1059da 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1059da 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x1059da 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x1059e0 [0x31, 0xC8] (fun s => s.RIP = 0x1059e0) (xorR32R32Effect 0x1059e0 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1059e0 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1059e0 0xc8 (by decide)) pre_rip
  have f55 : InstrSpec 0x1059e2 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x1059e2) (shlR32Effect 0x1059e2 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x1059e2 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x1059e2 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x1059e5 [0x31, 0xC1] (fun s => s.RIP = 0x1059e5) (xorR32R32Effect 0x1059e5 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1059e5 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1059e5 0xc1 (by decide)) pre_rip
  have f57 : InstrSpec 0x1059e7 [0x89, 0xC8] (fun s => s.RIP = 0x1059e7) (movR32R32Effect 0x1059e7 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1059e7 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x1059e7 0xc8 (by decide)) pre_rip
  have f58 : InstrSpec 0x1059e9 [0xD1, 0xE8] (fun s => s.RIP = 0x1059e9) (shrR32Effect 0x1059e9 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x1059e9 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x1059e9 0xe8 (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x1059eb [0x31, 0xC8] (fun s => s.RIP = 0x1059eb) (xorR32R32Effect 0x1059eb 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1059eb 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1059eb 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f40 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 126), (1, 130), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059b8) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f41 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 132), (1, 130), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059ba) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f42 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 134), (1, 130), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059bc) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f43 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 136), (1, 130), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059be) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f44 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 138), (1, 130), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059c3) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f45 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 138), (1, 140), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059c5) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f46 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 142), (1, 140), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059c7) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f47 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 144), (1, 140), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059c9) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.exec (n := 146) (ρ' := [(0, 144), (1, 140), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059ce) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f49 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 147), (1, 140), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059d3) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f50 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 147), (1, 149), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059d5) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f51 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 147), (1, 151), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059d8) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f52 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 147), (1, 153), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059da) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f53 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 147), (1, 155), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059e0) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f54 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 157), (1, 155), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059e2) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f55 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 157), (1, 159), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059e5) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f56 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 157), (1, 161), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059e7) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f57 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 163), (1, 161), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059e9) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f58 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 165), (1, 161), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059eb) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f59 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 167), (1, 161), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059ed) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_3 code

theorem rest_l10593a_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x10593a bytes_l10593a) [(0, 85), (1, 89), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      1172 0x10597a bytes_l10593a_1 b_l10593a_1 := by
  have f20 : InstrSpec 0x10597a [0x31, 0xC1] (fun s => s.RIP = 0x10597a) (xorR32R32Effect 0x10597a 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10597a 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10597a 0xc1 (by decide)) pre_rip
  have f21 : InstrSpec 0x10597c [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x10597c) (andR32Imm32Effect 0x10597c 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10597c 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x10597c 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x105982 [0x31, 0xC8] (fun s => s.RIP = 0x105982) (xorR32R32Effect 0x105982 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105982 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105982 0xc8 (by decide)) pre_rip
  have f23 : InstrSpec 0x105984 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x105984) (shlR32Effect 0x105984 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x105984 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x105984 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x105987 [0x31, 0xC1] (fun s => s.RIP = 0x105987) (xorR32R32Effect 0x105987 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105987 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105987 0xc1 (by decide)) pre_rip
  have f25 : InstrSpec 0x105989 [0x89, 0xC8] (fun s => s.RIP = 0x105989) (movR32R32Effect 0x105989 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105989 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105989 0xc8 (by decide)) pre_rip
  have f26 : InstrSpec 0x10598b [0xD1, 0xE8] (fun s => s.RIP = 0x10598b) (shrR32Effect 0x10598b 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x10598b 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x10598b 0xe8 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x10598d [0x31, 0xC8] (fun s => s.RIP = 0x10598d) (xorR32R32Effect 0x10598d 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10598d 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10598d 0xc8 (by decide)) pre_rip
  have f28 : InstrSpec 0x10598f [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x10598f) (andEaxImm32Effect 0x10598f 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x10598f 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x10598f 0x5050) pre_rip
  have f29 : InstrSpec 0x105994 [0x31, 0xC1] (fun s => s.RIP = 0x105994) (xorR32R32Effect 0x105994 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105994 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105994 0xc1 (by decide)) pre_rip
  have f30 : InstrSpec 0x105996 [0x01, 0xC0] (fun s => s.RIP = 0x105996) (addR32R32Effect 0x105996 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105996 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105996 0xc0 (by decide)) pre_rip
  have f31 : InstrSpec 0x105998 [0x31, 0xC8] (fun s => s.RIP = 0x105998) (xorR32R32Effect 0x105998 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105998 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105998 0xc8 (by decide)) pre_rip
  have f32 : InstrSpec 0x10599a [0x66, 0x89, 0x44, 0x24, 0x1E] (StorePre 0x10599a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x10599a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10599a 5 0 (.sib 4 none 0 (.d8 0x1e)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10599a 5 0 (.sib 4 none 0 (.d8 0x1e))).toInstrSpec (mov_m16_r16_effect_step 0x10599a 0 (.sib 4 none 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x10599f [0x0F, 0xB7, 0x44, 0x24, 0x20] (LoadPre 0x10599f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10599f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10599f 5 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10599f 5 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (movzx_r32_m16_effect_step 0x10599f 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f34 : InstrSpec 0x1059a4 [0x89, 0xC1] (fun s => s.RIP = 0x1059a4) (movR32R32Effect 0x1059a4 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1059a4 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1059a4 0xc1 (by decide)) pre_rip
  have f35 : InstrSpec 0x1059a6 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x1059a6) (shrR32Effect 0x1059a6 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1059a6 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x1059a6 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x1059a9 [0x31, 0xC1] (fun s => s.RIP = 0x1059a9) (xorR32R32Effect 0x1059a9 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1059a9 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x1059a9 0xc1 (by decide)) pre_rip
  have f37 : InstrSpec 0x1059ab [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x1059ab) (andR32Imm32Effect 0x1059ab 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1059ab 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x1059ab 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x1059b1 [0x31, 0xC8] (fun s => s.RIP = 0x1059b1) (xorR32R32Effect 0x1059b1 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1059b1 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x1059b1 0xc8 (by decide)) pre_rip
  have f39 : InstrSpec 0x1059b3 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x1059b3) (shlR32Effect 0x1059b3 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x1059b3 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x1059b3 0xe1 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 85), (1, 91), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10597c) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 85), (1, 93), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105982) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 93), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105984) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 95), (1, 97), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105987) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 95), (1, 99), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105989) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f25 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 101), (1, 99), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10598b) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 103), (1, 99), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10598d) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 105), (1, 99), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10598f) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f28 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 107), (1, 99), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105994) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f29 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 107), (1, 109), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105996) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f30 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 111), (1, 109), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105998) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f31 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 113), (1, 109), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10599a) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.exec (n := 115) (ρ' := [(0, 113), (1, 109), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10599f) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f33 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 116), (1, 109), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059a4) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f34 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 116), (1, 118), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059a6) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f35 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 116), (1, 120), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059a9) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f36 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 116), (1, 122), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059ab) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f37 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 116), (1, 124), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059b1) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f38 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 126), (1, 124), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059b3) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f39 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 126), (1, 128), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059b6) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_2 code

theorem rest_l10593a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10593a bytes_l10593a) (entryMap (live .l10593a))
      1192 0x10593a bytes_l10593a b_l10593a := by
  have f0 : InstrSpec 0x10593a [0x0F, 0xB7, 0x44, 0x24, 0x1C] (LoadPre 0x10593a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10593a + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10593a 5 0 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10593a 5 0 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (movzx_r32_m16_effect_step 0x10593a 0 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10593f [0x89, 0xC1] (fun s => s.RIP = 0x10593f) (movR32R32Effect 0x10593f 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10593f 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x10593f 0xc1 (by decide)) pre_rip
  have f2 : InstrSpec 0x105941 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105941) (shrR32Effect 0x105941 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105941 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105941 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105944 [0x31, 0xC1] (fun s => s.RIP = 0x105944) (xorR32R32Effect 0x105944 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105944 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105944 0xc1 (by decide)) pre_rip
  have f4 : InstrSpec 0x105946 [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x105946) (andR32Imm32Effect 0x105946 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105946 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x105946 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10594c [0x31, 0xC8] (fun s => s.RIP = 0x10594c) (xorR32R32Effect 0x10594c 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10594c 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10594c 0xc8 (by decide)) pre_rip
  have f6 : InstrSpec 0x10594e [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x10594e) (shlR32Effect 0x10594e 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10594e 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x10594e 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x105951 [0x31, 0xC1] (fun s => s.RIP = 0x105951) (xorR32R32Effect 0x105951 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105951 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105951 0xc1 (by decide)) pre_rip
  have f8 : InstrSpec 0x105953 [0x89, 0xC8] (fun s => s.RIP = 0x105953) (movR32R32Effect 0x105953 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105953 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x105953 0xc8 (by decide)) pre_rip
  have f9 : InstrSpec 0x105955 [0xD1, 0xE8] (fun s => s.RIP = 0x105955) (shrR32Effect 0x105955 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x105955 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x105955 0xe8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x105957 [0x31, 0xC8] (fun s => s.RIP = 0x105957) (xorR32R32Effect 0x105957 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105957 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105957 0xc8 (by decide)) pre_rip
  have f11 : InstrSpec 0x105959 [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105959) (andEaxImm32Effect 0x105959 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105959 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x105959 0x5050) pre_rip
  have f12 : InstrSpec 0x10595e [0x31, 0xC1] (fun s => s.RIP = 0x10595e) (xorR32R32Effect 0x10595e 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10595e 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10595e 0xc1 (by decide)) pre_rip
  have f13 : InstrSpec 0x105960 [0x01, 0xC0] (fun s => s.RIP = 0x105960) (addR32R32Effect 0x105960 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x105960 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x105960 0xc0 (by decide)) pre_rip
  have f14 : InstrSpec 0x105962 [0x31, 0xC8] (fun s => s.RIP = 0x105962) (xorR32R32Effect 0x105962 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105962 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105962 0xc8 (by decide)) pre_rip
  have f15 : InstrSpec 0x105964 [0x89, 0x84, 0x24, 0x1C, 0x01, 0x00, 0x00] (StorePre 0x105964 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11c)) s (0x105964 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105964 0 (.sib 4 none 0 (.d32 0x11c)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x105964 0 (.sib 4 none 0 (.d32 0x11c))).toInstrSpec (mov_m32_r32_low_effect_step 0x105964 0 (.sib 4 none 0 (.d32 0x11c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x10596b [0x66, 0x89, 0x44, 0x24, 0x1C] (StorePre 0x10596b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10596b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10596b 5 0 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10596b 5 0 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m16_r16_effect_step 0x10596b 0 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x105970 [0x0F, 0xB7, 0x44, 0x24, 0x1E] (LoadPre 0x105970 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x105970 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105970 5 0 (.sib 4 none 0 (.d8 0x1e)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105970 5 0 (.sib 4 none 0 (.d8 0x1e))).toInstrSpec (movzx_r32_m16_effect_step 0x105970 0 (.sib 4 none 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x105975 [0x89, 0xC1] (fun s => s.RIP = 0x105975) (movR32R32Effect 0x105975 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105975 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x105975 0xc1 (by decide)) pre_rip
  have f19 : InstrSpec 0x105977 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x105977) (shrR32Effect 0x105977 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x105977 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x105977 0xe9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10593f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105941) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105944) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 59), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105946) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 61), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10594c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 61), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10594e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 63), (1, 65), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105951) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 63), (1, 67), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105953) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 67), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105955) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 67), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105957) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 67), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105959) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 67), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10595e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 75), (1, 77), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105960) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 77), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105962) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 77), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105964) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 81), (1, 77), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10596b) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 81), (1, 77), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105970) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (1, 77), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105975) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 85), (1, 87), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105977) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 85), (1, 89), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10597a) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10593a_1 code

theorem block_l10593a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10593a :=
  Rest.liftedBlock (rest_l10593a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10593a x hx)

theorem rest_l10693d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10693d bytes_l10693d) (entryMap (live .l10693d))
      9 0x10693d bytes_l10693d b_l10693d := by
  have f0 : InstrSpec 0x10693d [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10693d) (movR64R64Effect 0x10693d 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10693d 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10693d 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106940 [0x48, 0x81, 0xC4, 0x38, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x106940) (addR64Imm32Effect 0x106940 4 0x138)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x106940 4 0x138).toInstrSpec (add_r64_imm32_effect_step 0x106940 0x48 0xc4 0x138 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106947 [0x5B] (PopPre 0x106947) (popR64Effect 0x106947 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106947 1 3).toInstrSpec (pop_r64_effect_step 0x106947 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x106948 [0x41, 0x5C] (PopPre 0x106948) (popR64Effect 0x106948 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106948 2 12).toInstrSpec (pop_r64_rex_effect_step 0x106948 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10694a [0x41, 0x5D] (PopPre 0x10694a) (popR64Effect 0x10694a 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10694a 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10694a 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10694c [0x41, 0x5E] (PopPre 0x10694c) (popR64Effect 0x10694c 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10694c 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10694c 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10694e [0x41, 0x5F] (PopPre 0x10694e) (popR64Effect 0x10694e 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10694e 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10694e 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x106950 [0x5D] (PopPre 0x106950) (popR64Effect 0x106950 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106950 1 5).toInstrSpec (pop_r64_effect_step 0x106950 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x106951 [0xC3] (RetPre 0x106951) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x106951).toInstrSpec (ret_effect_step 0x106951) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106940) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106947) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106948) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10694a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10694c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10694e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106950) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106951) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l10693d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10693d :=
  Rest.liftedBlock (rest_l10693d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10693d x hx)

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

theorem_by block_l1057c0_eval :
    program.runBlock (dialect code) ⟨.l1057c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1057f1_eval :
    program.runBlock (dialect code) ⟨.l1057f1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105825_eval :
    program.runBlock (dialect code) ⟨.l105825, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105856_eval :
    program.runBlock (dialect code) ⟨.l105856, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105870_eval :
    program.runBlock (dialect code) ⟨.l105870, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105880_eval :
    program.runBlock (dialect code) ⟨.l105880, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105892_eval :
    program.runBlock (dialect code) ⟨.l105892, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1058cb_eval :
    program.runBlock (dialect code) ⟨.l1058cb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1058d4_eval :
    program.runBlock (dialect code) ⟨.l1058d4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1058e4_eval :
    program.runBlock (dialect code) ⟨.l1058e4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1058f6_eval :
    program.runBlock (dialect code) ⟨.l1058f6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105929_eval :
    program.runBlock (dialect code) ⟨.l105929, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10693d_eval :
    program.runBlock (dialect code) ⟨.l10693d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
